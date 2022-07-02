import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Union

open Classical

-- 12. AxiomPowerSet
axiom AxiomPowerSet :
  ∀x: SetType, isSet (𝒫 x.1)

