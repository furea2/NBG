import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Foundation

open Classical

-- 15. AxiomGlobalChoice
axiom AxiomGlobalChoice :
  ∃F: Class, Function F → ∀x: Class, (hx: x∈U)
    → (¬ x＝ø → (∃y: Class, (hy: y∈x) → (OrdPair' x y hx (AllSetInU.1 ⟨x, hy⟩))∈F))

-- ex. AxiomChoice
theorem AxiomChoice :
  ∃x: Class, x∈U → ∃f: Class, Function f → ∀y: Class, (hy: y∈x)
    → (¬ y＝ø → (∃z: Class, (hz: z∈y) → (OrdPair' y z (AllSetInU.1 ⟨x, hy⟩) (AllSetInU.1 ⟨y, hz⟩))∈f)) := sorry

