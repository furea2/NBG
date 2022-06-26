import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Universe

open Classical

def isNotSelfIncluided (X : Class) : Prop :=
  ∃(Y:Class), ((X ∈ Y) ∧ (X ∉ X))
class NotSelfIncluided (X : Class) where
  isSelfIncluided : isNotSelfIncluided X

def NotSelfIncluidedIsInUniv (x : Class):
  isNotSelfIncluided x → isSet x := fun ⟨Y, h⟩ => ⟨Y, h.1⟩

theorem RusselClassExists:
  ∃A: Class, ∀x: Class,
    (x∈A) ↔ (isNotSelfIncluided x) := sorry

noncomputable def R := choose RusselClassExists

theorem Russel':
  (∃A : Class, ∀x : Class,
    (x ∈ A) ↔ (x ∉ x)) → False:= by {
  intro ⟨A, h⟩;
  have := h A;
  by_cases hA : A∈A;
  {have := this.1 hA; contradiction}
  {have := this.2 hA; contradiction}
}

theorem imp_symm {p q: Prop} : (p → q) → (¬ q → ¬ p) := sorry
theorem not_and_or {p q: Prop} : ¬(p ∧ q) → (¬ q ∨ ¬ p) := sorry

theorem UnivIsProper:
  isProper U := by {
  intro ⟨Y, hY⟩;
  have hUU := AllSetInU ⟨Y, hY⟩;
  have R_def := choose_spec RusselClassExists;
  sorry;
}

