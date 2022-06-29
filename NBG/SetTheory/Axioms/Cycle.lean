import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Membership

open Classical

-- 9. AxiomCycle
axiom AxiomCycle :
  ∀X: Class, ∃Y: Class, ∀u v w: Class,
    (hu: u∈U) → (hv: v∈U) → (hw: w∈U)
      → ((OrdPair' (OrdPair' u v hu hv) w (OrdPair_def' u v hu hv).1 hw) ∈ X
          ↔ (OrdPair' (OrdPair' w u hw hu) v (OrdPair_def' w u hw hu).1 hv) ∈ Y)

