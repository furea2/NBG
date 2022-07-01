import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.PowerSet

open Classical

-- 13. AxiomInfinity
axiom AxiomInfinity :
  ∃x: Class, x∈U
    ∧ ((ø∈x) ∧ ∀n: SetType, (
      (hn: n.1 ∈ x) → (n.1 ∪ {n}c) ∈ x))

def isInfinitySet (x: Class) :=
  x∈U
    → ((ø∈x) ∧ ∀n: SetType, (
      (hn: n.1 ∈ x) → (n.1 ∪ {n}c) ∈ x))

theorem IndClassExists:
  ∃Ind: Class, ∀x: Class,
    (x∈Ind) ↔ (isInfinitySet x) := sorry

noncomputable def Ind := choose IndClassExists

noncomputable def Omega := ⋂ Ind
notation "ω" => Omega

-- empty set
theorem EmptyClassIsSet: Set ø := by
{
  let x := choose AxiomInfinity;
  have in_x := (choose_spec AxiomInfinity).2.1;
  exact ⟨⟨x, in_x⟩, AllSetInU.1 ⟨x, in_x⟩⟩;
}

theorem EmptySet: SetType where
  X := ø
  x := EmptyClassIsSet
notation " ø_set " => EmptySet

-- finite set
def isFiniteSet (x: Class) :=
  ∃f: Class, Function f
    → (Dom f ＝ x) ∧ (Rng f ∈ ω)

class Finite where
  α : Class
  isFiniteSet : isFiniteSet α
