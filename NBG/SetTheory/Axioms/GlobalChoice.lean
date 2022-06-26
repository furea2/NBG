import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Foundation

open Classical

-- 15. AxiomGlobalChoice
axiom AxiomGlobalChoice :
  ∃F: Class, Function F → ∀x: Class, x∈U
    → (¬ x＝∅ → (∃y: Class, y∈x → ＜x,y＞∈F))

-- ex. AxiomChoice
theorem AxiomChoice :
  ∃x: Class, x∈U → ∃f: Class, Function f → ∀y: Class, y∈x
    → (¬ y＝∅ → (∃z: Class, z∈y → ＜y,z＞∈f)) := sorry

