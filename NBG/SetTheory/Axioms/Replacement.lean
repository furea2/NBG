import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Cycle

open Classical

-- 10. AxiomReplacement
axiom AxiomReplacement :
  ∀F x: Class, ∀(_: Function F), ∀(_: Set x),
    (h: x ∈ Dom F) → isSet (@Apply F x _ h)

