import Mathlib.Data.List.Range
import Mathlib.Data.Tree.Basic
import equational_theories.FreeMagma
import equational_theories.MagmaLaw

def formatShape : Tree Unit → String
  | .nil => "·"
  | .node _ lhs rhs => s!"({formatShape lhs} ◇ {formatShape rhs})"

def productWith {α β γ : Type} (xs : Array α) (ys : Array β) (f : α → β → γ) : Array γ :=
  xs.map (λ x => ys.map (f x)) |>.flatten

def shapesOfOrder : ℕ → Array (Tree Unit)
  | 0 => #[.nil]
  | numNodes =>
    let smaller := List.finRange numNodes |>.toArray.map (shapesOfOrder ·.val)
    Array.zipWith smaller smaller.reverse
      (λ lhs rhs => productWith lhs rhs (.node ()))
    |>.flatten

-- Connect to the Mathlib theory on cartesian trees
-- import Mathlib.Combinatorics.Enumerative.Catalan
-- def treesOfNumNodesEq_fromShapes (n : ℕ) : Finset (Tree Unit) :=
--   let trees : Array (Tree Unit) := shapesOfOrder n
--   trees.toList.toFinset
-- theorem set_treesOfNumNodesEq (n : ℕ) : (treesOfNumNodesEq_fromShapes n = Tree.treesOfNumNodesEq n) :=
--   sorry

def FreeMagma.comp {α : Type} [Ord α] (m1 m2 : FreeMagma α) : Ordering :=
  match m1, m2 with
    | .Leaf n,     .Leaf m     => compare n m
    | .Leaf _,     .Fork _ _   => .lt
    | .Fork _ _,   .Leaf _     => .gt
    | .Fork l1 r1, .Fork l2 r2 => (l1.comp l2).then (r1.comp r2)

def Law.MagmaLaw.comp {α : Type} [Ord α] (l1 l2 : Law.MagmaLaw α) : Ordering :=
  (FreeMagma.comp l1.lhs l2.lhs).then (FreeMagma.comp l1.rhs l2.rhs)

-- Canonically reorders variables
def FreeMagma.canonicalize (m : FreeMagma ℕ) : FreeMagma ℕ :=
  ((go m).run' #[]).run
where
  go : FreeMagma ℕ → StateM (Array ℕ) (FreeMagma ℕ)
  | .Leaf v =>   do pure <| .Leaf (← getInd v)
  | .Fork l r => do pure <| .Fork (← go l) (← go r)

  getInd (n : ℕ) : StateM (Array ℕ) ℕ := do
    let xs ← get
    match xs.indexOf? n with
    | some i => return i
    | none =>
      set (xs.push n)
      return xs.size

def Law.MagmaLaw.canonicalize (l : Law.NatMagmaLaw) : Law.NatMagmaLaw :=
  (go.run' #[]).run
where
  go : StateM (Array ℕ) Law.NatMagmaLaw := do
    let lhs' ← FreeMagma.canonicalize.go l.lhs
    let rhs' ← FreeMagma.canonicalize.go l.rhs
    return ⟨lhs', rhs'⟩

def Law.MagmaLaw.is_canonical (law : Law.MagmaLaw Nat) : Bool :=
  law.symm.canonicalize.comp law ≠ .lt

-- We care about the order of the results so we can't use a standard non-determinism monad
def VarAllocM (α : Type) := ℕ → Array (α × ℕ)

instance : Monad VarAllocM where
  pure x n := #[(x, n)]
  bind a f n := a n |>.map (λ (x, m) => f x m) |>.flatten

def VarAllocM.run {α : Type} (a : VarAllocM α) (nextVar : ℕ) : Array (α × ℕ) :=
  a nextVar

def VarAllocM.run' {α : Type} (a : VarAllocM α) (nextVar : ℕ) : Array α :=
  (a.run nextVar).map (·.1)

def nothing {α : Type} : VarAllocM α :=
  λ _ => #[]

def availableVars : VarAllocM ℕ :=
  λ nextVar => List.range (nextVar + 1) |>.toArray.map λ var => (var, max (var + 1) nextVar)

def exprsWithShape : Tree Unit → VarAllocM (FreeMagma ℕ)
  | .nil =>            do pure <| .Leaf (← availableVars)
  | .node _ lhs rhs => do pure <| .Fork (← exprsWithShape lhs) (← exprsWithShape rhs)

-- TODO: develop the theory of Bell numbers and show that it counts the expressions above

def lawsWithShape : Tree Unit → Array Law.NatMagmaLaw
  | .nil => unreachable!
  | .node _ lhs rhs =>
    (go lhs rhs).run' 0 |>.filter (·.is_canonical)
where
  go (lhs rhs : Tree Unit) : VarAllocM Law.NatMagmaLaw :=
    do pure ⟨← exprsWithShape lhs, ← exprsWithShape rhs⟩

def lawsOfOrder (order : ℕ) (includeRedundantTrivialLaws := false) : Array Law.NatMagmaLaw := Id.run do
  let mut laws := #[]
  for shape in shapesOfOrder (order + 1) do
    for law in lawsWithShape shape do
      if ¬includeRedundantTrivialLaws ∧ order > 0 ∧ law.lhs == law.rhs then
        continue
      laws := laws.push law
  pure laws

-- TODO: theorem that shows that this list includes an equivalent for each law of that order

def listLawsUpToOrder (maxOrder : ℕ) : Array Law.NatMagmaLaw :=
  List.range (maxOrder + 1) |>.toArray.map lawsOfOrder |>.flatten

def maxOrder : ℕ := 4

def main : IO Unit := do
  -- for order in List.range (maxOrder + 1) do
  --   for shape in shapesOfOrder order do
  --     IO.println (formatShape shape)
  for law in listLawsUpToOrder maxOrder do
    IO.println law
