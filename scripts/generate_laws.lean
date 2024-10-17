import Mathlib.Data.List.Range
import Mathlib.Data.Tree.Basic
import equational_theories.FreeMagma
import equational_theories.MagmaLaw

def Shape := Tree Unit

def formatShape : Shape → String
  | .nil => "·"
  | .node _ lhs rhs => s!"({formatShape lhs} ◇ {formatShape rhs})"

def productWith {α β γ : Type} (xs : Array α) (ys : Array β) (f : α → β → γ) : Array γ :=
  xs.map (λ x => ys.map (f x)) |>.flatten

def shapesOfOrder : ℕ → Array Shape
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

open Law
open FreeMagma

def subst (law : NatMagmaLaw) (vars : List ℕ) : NatMagmaLaw :=
  let aux := fmapFreeMagma (vars.get! ·)
  ⟨aux law.lhs, aux law.rhs⟩

local instance : Magma ℕ where
  op := max

def lastVar (law : NatMagmaLaw) : ℕ :=
  let aux := evalInMagma (· + 1)
  max (aux law.lhs) (aux law.rhs)

def equivalentLaws (law : NatMagmaLaw) : Array NatMagmaLaw :=
  let vars := List.range (lastVar law + 1)
  let renamings := (List.permutations vars).toArray.map (subst law)
  renamings ++ renamings.map (·.symm)

-- TODO: theorem that shows that these laws really are equivalent

-- We care about the order of the results so we can't use a standard non-determinism monad
def VarAllocM (α : Type) := ℕ → Array (α × ℕ)

instance : Monad VarAllocM where
  pure x n := #[(x, n)]
  bind a f n := a n |>.map (λ (x, m) => f x m) |>.flatten

def VarAllocM.run {α : Type} (a : VarAllocM α) (nextVar : ℕ) : Array (α × ℕ) :=
  a nextVar

def VarAllocM.run' {α : Type} (a : VarAllocM α) (nextVar : ℕ) : Array α :=
  (a.run nextVar).map (·.1)

def availableVars : VarAllocM ℕ :=
  λ nextVar => List.range (nextVar + 1) |>.toArray.map λ var => (var, max (var + 1) nextVar)

def exprsWithShape : Shape → VarAllocM (FreeMagma ℕ)
  | .nil =>
    do pure <| .Leaf (← availableVars)
  | .node _ lhs rhs =>
    do pure <| .Fork (← exprsWithShape lhs) (← exprsWithShape rhs)

-- TODO: develop the theory of Bell numbers and show that it counts the expressions above

def lawsWithShape : Shape → Array NatMagmaLaw
  | .nil => unreachable!
  | .node _ lhs rhs =>
    let m := do pure <| MagmaLaw.mk (← exprsWithShape lhs) (← exprsWithShape rhs)
    m.run' 0

local instance : Hashable NatMagmaLaw where
  hash law := hash (toString law)  -- Yuck

def lawsOfOrder (order : ℕ) (includeRedundantTrivialLaws := false) : Array NatMagmaLaw := Id.run do
  let mut laws := #[]
  let mut lawsSet : Std.HashSet NatMagmaLaw := {}
  for shape in shapesOfOrder (order + 1) do
    for law in lawsWithShape shape do
      if ¬includeRedundantTrivialLaws ∧ order > 0 ∧ law.lhs == law.rhs then
        continue
      let equivalents := equivalentLaws law
      if equivalents.all (¬lawsSet.contains ·) then
        laws := laws.push law
        lawsSet := lawsSet.insert law
  pure laws

-- TODO: theorem that shows that this list includes an equivalent for each law of that order

def listLawsUpToOrder (maxOrder : ℕ) : Array NatMagmaLaw :=
  List.range (maxOrder + 1) |>.toArray.map lawsOfOrder |>.flatten

def maxOrder : Nat := 4

def main : IO Unit := do
  -- for order in List.range (maxOrder + 1) do
  --   for shape in shapesOfOrder order do
  --     IO.println (formatShape shape)
  for law in listLawsUpToOrder maxOrder do
    IO.println law
