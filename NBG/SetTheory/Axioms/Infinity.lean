import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.PowerSet

open Classical

-- 13. AxiomInfinity
axiom AxiomInfinity :
  ∃x: Class, x∈U
    ∧ ((ø∈x) ∧ ∀n: Class, (
      (hn: n∈x) → (n ∪ (Pair' n n (AllSetInU.1 ⟨x, hn⟩) (AllSetInU.1 ⟨x, hn⟩))) ∈ x))

def isInfinitySet (x: Class) :=
  x∈U
    → ((ø∈x) ∧ ∀n: Class, (
      (hn: n∈x) → (n ∪ (Pair' n n (AllSetInU.1 ⟨x, hn⟩) (AllSetInU.1 ⟨x, hn⟩))) ∈ x))

theorem IndClassExists:
  ∃Ind: Class, ∀x: Class,
    (x∈Ind) ↔ (isInfinitySet x) := sorry

noncomputable def Ind := choose IndClassExists

noncomputable def Omega := ⋂ Ind
notation "ω" => Omega

def isFiniteSet (x: Class) :=
  ∃f: Class, Function f
    → (Dom f ＝ x) ∧ (Rng f ∈ ω)

class Finite where
  α : Class
  isFiniteSet : isFiniteSet α
