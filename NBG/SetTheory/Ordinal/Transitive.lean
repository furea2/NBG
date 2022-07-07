import NBG.SetTheory.Axioms.Basic
open Classical

def isTransitive (X: Class) :=
  ∀(y z: Class),(y∈X) → (z∈y) → z ∈ X
class Transitive (X: Class) where
  isTransitive: isTransitive X

theorem TrClassisExists:
  ∃(Tr: Class), ∀(z: Class),
    (z∈Tr) ↔ ((z∈U) ∧ (isTransitive z)) := sorry

noncomputable def Tr : Class := choose TrClassisExists
noncomputable def Tr_def:
∀(z: Class),
    (z∈Tr) ↔ ((z∈U) ∧ (isTransitive z)) :=
  choose_spec TrClassisExists

theorem TrIsInductive: isInductive Tr := sorry
theorem OmegaIsInductive: isTransitive ω := sorry

theorem OmegaIsInTr: ω ⊂ Tr := sorry
theorem OmegaSubsetTr: ω ∈ Tr := sorry

