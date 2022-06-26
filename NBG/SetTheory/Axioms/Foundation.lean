import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Infinity

open Classical

-- 14. AxiomFoundation
axiom AxiomFoundation :
  ∀x: Class, x∈U
    → ¬ x＝∅ → (∃y: Class, y∈x → (∀z: Class, z∈y → z∉x))
