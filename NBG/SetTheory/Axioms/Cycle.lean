import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Membership

open Classical

-- 9. AxiomCycle
axiom AxiomCycle :
  ∀X: Class, ∃Y: Class, ∀u v w: SetType,
    ＜u,v,w＞c ∈ X ↔ ＜w,u,v＞c ∈ Y

