import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Inversion

open Classical

-- 7. AxiomDomain
axiom AxiomDomain :
  ∀X: Class, ∃D: Class,
    ∀x: Class, (hx: x∈U) → (x∈D ↔ ∃y: SetType,
      (＜(SetType.mk₂ x hx), y＞c ∈ X))
noncomputable def Dom (X: Class) := choose (AxiomDomain X)
noncomputable def Dom_def (X: Class) := choose_spec (AxiomDomain X)
noncomputable def Rng (X: Class) := choose (AxiomDomain (RelInv X))
noncomputable def Rng_def (X: Class) := choose_spec (AxiomDomain (RelInv X))

