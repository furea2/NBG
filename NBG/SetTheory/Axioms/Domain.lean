import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Inversion

open Classical

-- 7. AxiomDomain
axiom AxiomDomain :
  ∀X: Class, ∃D: Class,
    ∀x: SetType, (x.1∈D ↔ ∃y: SetType, (＜x, y＞c ∈ X))
noncomputable def Dom (X: Class) := choose (AxiomDomain X)
noncomputable def Rng (X: Class) := choose (AxiomDomain (RelInv X))

