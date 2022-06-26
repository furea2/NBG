import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Union

open Classical

-- 12. AxiomPowerSet
axiom AxiomPowerSet :
  ∀x: Class, ∃Z: Class,
    ∀y: Class, y∈Z ↔ (∀z: Class, z∈y → z∈x)

