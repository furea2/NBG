import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Domain

open Classical

-- 8. AxiomMembership
axiom AxiomMembership :
  ∃E: Class,
    ∀x y: Class, ∃_: Set x, ∃_: Set y,
      (＜x, y＞ ∈ E ↔ x∈y)

-- class E
noncomputable def E: Class := choose AxiomMembership
noncomputable def E_def:
  ∀x y: Class, ∃_: Set x, ∃_: Set y,
    (＜x, y＞ ∈ E ↔ x∈y) :=
  choose_spec AxiomMembership

theorem DomEEqUniv : (Dom E) ＝ U := sorry

-- Image type
theorem ImageClassExists (R X: Class) [Relation R]:
  ∃Im: Class, ∀y: Class, ∃_: Set y,
    ((y ∈ Im)
      ↔ (∃x: Class, ∃(hx:x ∈ X), ((@OrdPair_mk x y (Set.mk₁ hx) _)∈ R))) := by {
  sorry;
}
noncomputable def Im (R X: Class) [Relation R]: Class :=
  choose (ImageClassExists R X)
noncomputable def ImageClass_def (R X: Class) [Relation R]:
  ∀y: Class, ∃_: Set y,
      ((y ∈ (Im R X))
        ↔ (∃x: Class, ∃(hx:x ∈ X), ((@OrdPair_mk x y (Set.mk₁ hx) _)∈ R))) :=
  choose_spec (ImageClassExists R X)

theorem PreImageClassExists (R X: Class) [Relation R]:
  ∃PreIm: Class, ∀y: Class, ∃_: Set y,
    ((y ∈ PreIm)
      ↔ (∃x: Class, ∃(hx:x ∈ X), ((@OrdPair_mk x y (Set.mk₁ hx) _)∈ (RelInv R)))) :=
  @ImageClassExists (RelInv R) X ⟨RelInvRelationIsRelation⟩


-- Function type
def isFunction (F : Class) [Relation F] : Prop :=
  ∀x x' y y': Class, ∀_: Set x, ∀_: Set x', ∀_: Set y, ∀_: Set y',
    ＜x, y＞ ∈ F → ＜x', y'＞ ∈ F → x ＝x' → y ＝ y'
class Function (F : Class) extends Relation F where
  isFunction : isFunction F

noncomputable def Apply (F x: Class) [hx: Set x] {h: x ∈ (Dom F)} : Class :=
  choose ((Dom_def F x hx).1 h)
noncomputable def TargetIsSet (F x: Class) [hx: Set x] {h: x ∈ (Dom F)} : Set (@Apply F x _ h) :=
  choose (choose_spec ((Dom_def F x hx).1 h))
noncomputable def Apply_def (F x: Class) [hx: Set x] {h: x ∈ (Dom F)}:
  (@OrdPair_mk x (@Apply F x _ h) _ (TargetIsSet _ _)) ∈ F :=
  choose_spec (choose_spec ((Dom_def F x hx).1 h))

theorem ApplyFunctionUniqueTarget (F x x': Class) [set_x:Set x] [set_x':Set x']
    {hx: x ∈ (Dom F)} {hx': x' ∈ (Dom F)} [hF: Function F]:
      x ＝ x' →  @Apply F x set_x hx ＝ @Apply F x' set_x' hx' := by {
  let y := @Apply F x set_x hx;
  let y' := @Apply F x' set_x' hx';
  have set_y: Set y := @TargetIsSet F x set_x hx;
  have set_y': Set y' := @TargetIsSet F x' set_x' hx';
  have F_def: ＜x, y＞ ∈ F → ＜x', y'＞ ∈ F
    → x ＝ x' → y ＝ y' :=
    hF.2 x x' y y' set_x set_x' set_y set_y';
  have hxy: ＜x, y＞ ∈ F := @Apply_def F x set_x hx;
  have hxy': ＜x', y'＞ ∈ F := @Apply_def F x' set_x' hx';
  exact fun h => F_def hxy hxy' h;
}

-- define useful notation
noncomputable def as_map (F : Class) [Relation F]: (x: Class) → {_: x ∈ Dom F} → Class := by
exact fun x hx => @Apply F x (Set.mk₁ hx) hx
notation F"【"x"】" => as_map F x

-- injective, surjective, bijective

-- Todo


-- restriction
noncomputable def Restriction (F X: Class) := F ∩ (X ✕ U)
infix:50 " ↾ "  => Restriction

-- UnionAll
noncomputable def UnionAll_mk' (X : Class) :=
  Dom (E ∩ (U ✕ X))
noncomputable instance : HasUnionAll Class where
  UnionAll := UnionAll_mk'

-- InterAll
noncomputable def InterAll_mk' (X : Class) :=
  Diff U (Dom ((Diff U₂ E) ∩ (U ✕ X)))
noncomputable instance : HasInterAll Class where
  InterAll := InterAll_mk'

-- PowerClass
noncomputable def PowerClass_mk' (X : Class) : Class :=
  Diff U (Dom ((RelInv E) ∩ (U ✕ (Diff U X))))
noncomputable def PowerClass_def' (X : Class) :=
  Diff_def U (Dom ((RelInv E) ∩ (U ✕ (Diff U X))))

def isPowerClass (PX : Class) :=
  ∃(X: Class) ,∀(Y: Class), Y ∈ PX ↔ Y ⊂ X
class PowerClass (PX : Class) where
  isPowerClass: isPowerClass PX

-- private theorem ImpIffNotImpNot {p q: Prop}: (p → q) ↔ (¬ q → ¬ p):= sorry
-- private theorem IffIffNotIffNot {p q: Prop}: (p ↔ q) ↔ (¬ q ↔ ¬ p):= sorry
-- private theorem NotExIffAllNot {α: Type u} {p: α → Prop}:
--   ¬ (∃(x : α), p x) ↔ (∀(y: α), ¬ p y) := sorry
-- private theorem NotJoinIffNotUnionNot {X Y: Class}:
--   ∀(z: Class), (¬ (z ∈ (X ∩ Y)) ↔ (¬ z ∈ X) ∨ (¬ z ∈ Y)) := sorry
-- private theorem NotNotIff {p: Prop}: p ↔ ¬ ¬ p:= sorry

theorem PowerClass_def'_is_PowerClass:
  isPowerClass (PowerClass_mk' X) := by {
--   exists X;
--   intro Y;
--   apply Iff.intro;
--   {
--     -- intro h z hz;
--     -- have PX_def := PowerClass_def' X;
--     -- have hPX := ((PX_def Y).1 h).2;
--     -- have hY : Y ∈ U := AllSetInU.1 ⟨(PowerClass' X), h⟩;
--     -- clear PX_def h;
--     -- -- have PX_set := SetType.mk₂ Y ((PX_def Y).1 h).1;
--     -- -- clear PX_def h;
--     -- have Dom_def1 := Dom_def (RelInv E ∩ (U ✕ Diff U X));
--     -- have h1 := (Dom_def1 Y) hY;
--     -- clear Dom_def1;
--     -- rw [IffIffNotIffNot] at h1;
--     -- have h2 := h1.2 hPX;
--     -- clear h1 hPX;
--     -- rw [NotExIffAllNot] at h2;
--     -- have h3 := h2 (SetType.mk₁ z ⟨Y, hz⟩);
--     -- clear h2;
--     -- rw [NotJoinIffNotUnionNot] at h3;
--     -- cases h3;
--     -- case mp.inl h3 => {sorry;}
--     -- case mp.inr h3 => {
--     --   -- have hxy := ＜(SetType.mk₂ Y hY), (SetType.mk₁ z ⟨Y, hz⟩)＞c;
--     --   have prod_def := (Product_def U (Diff U X)) ＜(SetType.mk₂ Y hY), (SetType.mk₁ z ⟨Y, hz⟩)＞c;
--     --   rw [IffIffNotIffNot] at prod_def;
--     --   have h4 := prod_def.2 h3;
--     --   clear prod_def h3;
--     --   /-
--     --   X Y z : Class
--     --   hz : z ∈ Y
--     --   hY : Y ∈ U
--     --   h4 : ¬∃ x y, SetType.X ∈ U → SetType.X ∈ Diff U X → ＜SetType.mk₂ Y hY,SetType.mk₁ z (_ : ∃ Y, z ∈ Y)＞c ＝ ＜x,y＞c
--     --   ⊢ z ∈ X
--     --   -/

--     --   have h5 : (¬∃ x y, (SetType.mk₂ Y hY).X ∈ U
--     --     → (SetType.mk₁ z ⟨Y, hz⟩).X ∈ Diff U X → ＜(SetType.mk₂ Y hY),(SetType.mk₁ z ⟨Y, hz⟩)＞c ＝ ＜x,y＞c)
--     --     ↔ (¬∃ x y, (SetType.mk₂ Y hY).X ∈ U
--     --     → (SetType.mk₁ z ⟨Y, hz⟩).X ∈ Diff U X → ¬ ¬ ＜(SetType.mk₂ Y hY),(SetType.mk₁ z ⟨Y, hz⟩)＞c ＝ ＜x,y＞c) := by {
--     --       sorry;
--     --     }
--       -- have h6 := h5.1 h4;
--       -- rw [h5, NotNotIff] at h4;
--       -- have h5 := ImpIffNotImpNot.2 h4;
--       -- rw [IffIffNotIffNot] at h4
--       -- sorry;}
--     sorry;
--   }
--   {sorry;}
  sorry;
}

noncomputable instance : HasPow Class where
  Pow := PowerClass_mk'

theorem UnivIsClosedPowerSet:
  U ＝ 𝒫 U := sorry

