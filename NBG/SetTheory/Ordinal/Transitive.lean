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

def isInductive (X: Class) :=
  ((ø∈X) ∧ ∀x: Class,
    ((hn: x ∈ X) → (x ∪ (@Singleton_mk x (Set.mk₁ hn))) ∈ X))
class Inductive (x: Class) where
  isInductive: isInductive x

theorem TrIsInductive: isInfinitySet Tr := sorry
theorem OmegaIsInductive: isInfinitySet ω := sorry

theorem OmegaIsInTr: ω ⊂ Tr := sorry
theorem OmegaSubsetTr: ω ∈ Tr := sorry

