import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Foundation

open Classical

-- 15. AxiomGlobalChoice
axiom AxiomGlobalChoice:
  ∃F: Class, Function F → ∀x: SetType,
    (¬ x.1＝ø → (∃y: SetType, (＜x, y＞c ∈ F)))

-- ex. AxiomChoice
theorem AxiomChoice:
  ∃x: SetType, ∃f: Class, Function f → ∀y: SetType,
    (¬ y.1＝ø → (∃z: SetType, (＜y, z＞c ∈ f))) := sorry

