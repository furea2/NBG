import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Cycle

open Classical

-- 10. AxiomReplacement
axiom AxiomReplacement :
  ∀F x: Class, ∀(hF: Function F), ∀(_: Set x),
    isSet (@Im F x hF.1)



