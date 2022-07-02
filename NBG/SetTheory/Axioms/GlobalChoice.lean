import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Foundation

open Classical

-- 15. AxiomGlobalChoice
axiom AxiomGlobalChoice:
  ∃F: Class,∃_: Function F,∀x: Class, ∀_: Set x,
    (¬ x＝ø → (∃y: Class,∃hy: y∈x,
      (@Pair_mk x y _ (Set.mk₁ hy)) ∈ F))

-- ex. AxiomChoice
theorem AxiomChoice:
  ∀x: Class, ∀_: Set x,
    ∃f: Class, ∃_: Function f, ∀y: Class, ∃hy: y∈x,
      (¬ y＝ø → (∃z: Class,∃hz: z∈y,
        ((@Pair_mk y z (Set.mk₁ hy) (Set.mk₁ hz)) ∈ f))) := sorry

