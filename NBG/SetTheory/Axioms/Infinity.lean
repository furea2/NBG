import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.PowerSet

open Classical

-- 13. AxiomInfinity
axiom AxiomInfinity :
  ∃x: Class, x∈U
    → ((∅∈x) ∧ ∀n: Class, (n∈x → (n ∪ {n}) ∈ x))

noncomputable def Zero : Class := ∅
noncomputable def One : Class := {Zero}
noncomputable def Two : Class := {Zero, One}
-- noncomputable def Three : Class := {Zero, One, Two}

def isInfinitySet (x: Class) :=
  x∈U
    → ((∅∈x) ∧ ∀n: Class, (n∈x → (n ∪ {n}) ∈ x))

theorem IndClassExists:
  ∃Ind: Class, ∀x: Class,
    (x∈Ind) ↔ (isInfinitySet x) := sorry

noncomputable def Ind := choose IndClassExists

noncomputable def Omega := ⋂ Ind
notation "ω" => Omega
notation "ℕ" => Diff Omega {∅}

def isFiniteSet (x: Class) :=
  ∃f: Class, Function f
    → (Dom f ＝ x) ∧ (Rng f ∈ ω)

class Finite where
  α : Class
  isFiniteSet : isFiniteSet α


