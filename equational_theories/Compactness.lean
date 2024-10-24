import Mathlib.Data.Finset.Basic
import equational_theories.Completeness

open Law

set_option linter.unusedVariables false
def derive.getAxioms {α} [DecidableEq α] {Γ : Ctx α} {E : MagmaLaw α} (h : Γ ⊢ E) :
    Finset (MagmaLaw α) :=
  match h with
  | .Ax _ => {E}
  | .Ref => {}
  | .Sym h => derive.getAxioms h
  | .Trans h₁ h₂ => derive.getAxioms h₁ ∪ derive.getAxioms h₂
  | .Subst _ h => derive.getAxioms h
  | .Cong h₁ h₂ => derive.getAxioms h₁ ∪ derive.getAxioms h₂

def ToCtx {α} (S : Finset (MagmaLaw α)) : Ctx α := S

instance Ctx.hasSubset {α} : HasSubset (Ctx α) := Set.instHasSubset

def derive.Weak {α} {Γ Δ : Ctx α} {E : MagmaLaw α} (inc : Γ ⊆ Δ) (h : Γ ⊢ E) :
    Δ ⊢ E := by
  cases h
  case Ax => refine derive.Ax (inc ?_); assumption
  case Ref => exact derive.Ref
  case Sym => apply derive.Sym ; apply derive.Weak _ <;> trivial
  case Trans => apply derive.Trans <;> try apply derive.Weak <;> assumption
  case Subst => apply derive.Subst ; apply derive.Weak <;> assumption
  case Cong => apply derive.Cong <;> apply derive.Weak <;> assumption

def derive.getAxiomsEnough {α} [DecidableEq α] {Γ : Ctx α} {E : MagmaLaw α} (h : Γ ⊢ E) :
    ToCtx (derive.getAxioms h) ⊢ E := by
  cases h <;> simp [ToCtx, getAxioms]
  case Ax => constructor; rfl
  case Ref => exact derive.Ref
  case Sym _ _ h => exact derive.Sym (derive.getAxiomsEnough _)
  case Trans _ _ _ h₁ h₂ =>
    apply derive.Trans
    · exact derive.Weak Set.subset_union_left (derive.getAxiomsEnough h₁)
    · exact derive.Weak Set.subset_union_right (derive.getAxiomsEnough h₂)
  case Subst => exact derive.Subst _ (derive.getAxiomsEnough _)
  case Cong _ _ _ h₁ h₂ =>
    exact derive.Cong (derive.Weak Set.subset_union_left (derive.getAxiomsEnough h₁))
      (derive.Weak Set.subset_union_right (derive.getAxiomsEnough h₂))

def Compactness {α} [DecidableEq α] {Γ : Ctx α} {E : MagmaLaw α} (h : Γ ⊧ E) :
    ∃ (Δ : Finset (MagmaLaw α)), Nonempty <| ToCtx Δ ⊧ E := by
  have ⟨h''⟩ := Completeness h
  exact ⟨derive.getAxioms h'', ⟨Soundness (derive.getAxiomsEnough _)⟩⟩
