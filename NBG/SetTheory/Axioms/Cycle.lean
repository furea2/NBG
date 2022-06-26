import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Membership

open Classical

-- 9. AxiomCycle
axiom AxiomCycle :
  ∀X: Class, ∃Y: Class, ∀u v w: Class,
    u∈U → v∈U → w∈U → (＜u,v,w＞∈X ↔ ＜w,u,v＞∈Y)

