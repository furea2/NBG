import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.PowerSet

open Classical

-- 13. AxiomInfinity
axiom AxiomInfinity :
  ∃x: Class, x∈U
    → ((ø∈x) ∧ ∀n: Class, (n∈x → (n ∪ {n}) ∈ x))

def isInfinitySet (x: Class) :=
  x∈U
    → ((ø∈x) ∧ ∀n: Class, (n∈x → (n ∪ {n}) ∈ x))

theorem IndClassExists:
  ∃Ind: Class, ∀x: Class,
    (x∈Ind) ↔ (isInfinitySet x) := sorry

noncomputable def Ind := choose IndClassExists

noncomputable def Omega := ⋂ Ind
notation "ω" => Omega
notation "ℕ" => Omega
notation "ℕ+" => Diff Omega {ø}

def isFiniteSet (x: Class) :=
  ∃f: Class, Function f
    → (Dom f ＝ x) ∧ (Rng f ∈ ω)

class Finite where
  α : Class
  isFiniteSet : isFiniteSet α

noncomputable def ClassOfNat (n : Nat) : Class :=
  match n with
    | 0     => ø
    | n + 1 => (ClassOfNat n) ∪ {ClassOfNat n}

noncomputable instance : OfNat Class n where
  ofNat := ClassOfNat n

