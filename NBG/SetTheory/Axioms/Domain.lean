import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Inversion

open Classical

-- 7. AxiomDomain
axiom AxiomDomain :
  ∀X: Class, ∃D: Class,
    ∀x: Class, (hx: x∈U) → (x∈D ↔ ∃y: Class, ((hy: y∈U) → (OrdPair' x y hx hy)∈X))
noncomputable def Dom (X: Class) := choose (AxiomDomain X)
noncomputable def Rng (X: Class) := choose (AxiomDomain (RelInv X))

