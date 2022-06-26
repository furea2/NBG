import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Replacement

open Classical

-- 11. AxiomUnion
axiom AxiomUnion :
  ∀x: Class, ∃Z: Class,
    ∀z: Class, z∈Z ↔ (∃y: Class, y∈x → z∈y)

