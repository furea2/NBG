import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Membership

open Classical

-- 9. AxiomCycle
axiom AxiomCycle :
  ∀X: Class, ∃Y: Class, ∀u v w: Class,
    ∃_: Set u, ∃_: Set v, ∃_: Set w,
      ＜u,v,w＞ ∈ X ↔ ＜w,u,v＞ ∈ Y

