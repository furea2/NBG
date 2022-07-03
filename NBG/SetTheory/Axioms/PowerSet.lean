import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Union

open Classical

-- 12. AxiomPowerSet
axiom AxiomPowerSet :
  ∀x: Class, Set x → isSet (𝒫 x)

