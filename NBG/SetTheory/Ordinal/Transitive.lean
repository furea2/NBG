import NBG.SetTheory.Axioms.Basic
open Classical

def isTransitive (X: Class) :=
  ∀(y z: Class),(y∈X) → (z∈y) → z ∈ X
class Transitive (X: Class) where
  isTransitive: isTransitive X

theorem TrClassisExists:
  ∃(Tr: Class), ∀(z: Class),
    (z∈Tr) ↔ ((z∈U) ∧ (isTransitive z)) := sorry

noncomputable def Tr : Class := (choose TrClassisExists)
noncomputable def Tr_def := (choose_spec TrClassisExists)

def isInductive (X: Class) :=
  ((ø∈X) ∧ ∀x: SetType,
    ((hn: x.1∈X) → (x.1 ∪ {x}c) ∈ X))

theorem TrIsInductive: isInfinitySet Tr := sorry


theorem OmegaIsInTr: ω ⊂ Tr := sorry
theorem OmegaSubsetTr: ω ∈ Tr := sorry

