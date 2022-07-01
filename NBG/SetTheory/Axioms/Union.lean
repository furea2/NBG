import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Replacement

open Classical

-- 11. AxiomUnion
axiom AxiomUnion:
  ∀x: Class, (x ∈ U) → ∃Z: Class,
    (Z ∈ U) ∧ (∀z: Class, z∈Z ↔ (∃y: Class, y∈x → z∈y))

noncomputable def UnionSet (x: Class) [hx: Set x] :=
  choose (AxiomUnion x hx.2)
noncomputable def UnionSet_def (x: Class) [hx: Set x] :=
  choose_spec (AxiomUnion x hx.2)

-- theorem ImpIffNotImpNot {p q : Prop} : (p → q) ↔ (¬ q → ¬ p) := sorry
-- theorem IffIffNotIffNot {p q : Prop} : (p ↔ q) ↔ (¬ q ↔ ¬ p) := sorry
-- theorem NotAndIffOrNot {p q : Prop} : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q := sorry
-- theorem NotOrIffAndNot {p q : Prop} : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q := sorry

-- def UnionIffFromAxiomUnion (X Y: Class) [x: Set X] [y: Set Y]:
--   @UnionSet {X, Y}c {x, y}s ＝ (X∪Y) := by {
--   rw [AxiomExtensionality];
--   intro z; 
--   have u_def1 := (@UnionSet_def {X, Y}c {x, y}s).2 z;
--   have u_def2 := UnionIntro X Y z;
--   have p_def  := (Pair_def X Y).2;
--   apply Iff.trans u_def1;
--   apply Iff.trans _ u_def2.symm;
--   clear u_def1 u_def2;
--   apply Iff.intro;
--   {
--     intro ⟨u, hz⟩;
--     by_cases hX: u ＝ X;
--     {
--       have hu := hz ((p_def u).2 (Or.inl hX));
--       exact Or.inl (((AxiomExtensionality u X).1 hX z).1 hu);
--     }
--     {
--       by_cases hY: u ＝ Y;
--       {
--         have hu := hz ((p_def u).2 (Or.inr hY));
--         exact Or.inr (((AxiomExtensionality u Y).1 hY z).1 hu);
--       }
--       {
--         sorry;
--       }
--     }
--   }
--   {
--     intro h;
--     cases h;
--     case mpr.inl h => {exact ⟨X, fun _ => h⟩;}
--     case mpr.inr h => {exact ⟨Y, fun _ => h⟩;}
--   }
-- }



def UnionIsSet (x y: Class) [Set X] [Set Y] : Set (x∪y) := sorry


