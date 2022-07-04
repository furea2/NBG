import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Domain

open Classical

-- 8. AxiomMembership
axiom AxiomMembership :
  ∃E: Class,
    ∀x y: Class, ∀_: Set x, ∀_: Set y,
      (＜x, y＞ ∈ E ↔ x∈y)

-- class E
noncomputable def E: Class := choose AxiomMembership
noncomputable def E_def:
  ∀x y: Class, ∀_: Set x, ∀_: Set y,
    (＜x, y＞ ∈ E ↔ x∈y) :=
  choose_spec AxiomMembership

theorem DomEEqUniv : (Dom E) ＝ U := sorry

-- Image type
theorem ImageClassExists (R X: Class) [hR: Relation R]:
  ∃Im: Class, ∀y: Class, ∀_: Set y,
    ((y ∈ Im)
      ↔ (∃x: Class, ∃(hx:x ∈ X), ((@OrdPair_mk x y (Set.mk₁ hx) _)∈ R))) := by {
  have : Relation (R ∩ (X ✕ U)) := sorry;
  let im := Rng (R ∩ (X ✕ U));
  let im_def := Rng_def (R ∩ (X ✕ U));
  have relinv_def := RelInv_def (R ∩ (X ✕ U));
  exists im;
  intro y hy;
  apply Iff.intro;
  {
    intro h;
    have ⟨x, hx, h_yx_in ⟩ := (im_def y hy).1 h;
    have ⟨x', y', set_x', set_y', h_xy_in', heq'⟩ := (relinv_def ＜y, x＞).1 h_yx_in;
    rw [IntersectionClassIntro] at h_xy_in';
    have ⟨x'', y'', hx'', hy'', heq''⟩ := (ProductClass_def X U ＜x', y'＞).1 h_xy_in'.2;
    have set_x'' := Set.mk₁ hx'';
    have set_y'' := Set.mk₁ hy'';
    rw [OrdPairEq] at heq';
    rw [OrdPairEq] at heq'';
    have heq': x'' ＝ x ∧ y ＝ y :=
      ⟨ClassEq.trans (ClassEq.symm heq''.1) (ClassEq.symm heq'.2), ClassEq.refl y⟩;
    have hx''_in:= (hR.1 ＜x'', y＞).2 ⟨x, y,_ ,_,OrdPairEq.2 heq'⟩;
    exists x'', hx'';
  }
  {
    intro ⟨x, x_in_X, xy_in_R⟩;
    have set_x := Set.mk₁ x_in_X;
    apply (im_def y hy).2;
    clear im_def;
    exists x, set_x;
    apply (relinv_def ＜y, x＞).2;
    clear relinv_def;
    -- have := hR.1 ＜x,y＞;
    have h_xy_in: ＜x,y＞ ∈ (R ∩ (X ✕ U)):= by {
      rw [IntersectionClassIntro];
      apply And.intro;
      {trivial;}
      {
        apply (ProductClass_def X U ＜x, y＞).2;
        exists x, y, x_in_X, hy.2;
        exact ClassEq.refl _;
      }
    }
    exists x,y,set_x,hy, h_xy_in;
    exact (ClassEq.refl ＜y, x＞);
  }
}
noncomputable def Im (R X: Class) [Relation R]: Class :=
  choose (ImageClassExists R X)
noncomputable def ImageClass_def (R X: Class) [Relation R]:
  ∀y: Class, ∀_: Set y,
      ((y ∈ (Im R X))
        ↔ (∃x: Class, ∃(hx:x ∈ X), ((@OrdPair_mk x y (Set.mk₁ hx) _)∈ R))) :=
  choose_spec (ImageClassExists R X)

theorem PreImageClassExists (R X: Class) [Relation R]:
  ∃PreIm: Class, ∀y: Class, ∀_: Set y,
    ((y ∈ PreIm)
      ↔ (∃x: Class, ∃(hx:x ∈ X), ((@OrdPair_mk x y (Set.mk₁ hx) _)∈ (RelInv R)))) :=
  @ImageClassExists (RelInv R) X ⟨RelInvRelationIsRelation⟩


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

/-- The brige theorem of image and function, namely f[X] = {f(x)}. -/
theorem SingleSetFunctionImageIsSingleton (F x: Class) [hx: Set x] {h: x ∈ (Dom F)} [hF: Function F]:
  Im F x ＝ @Singleton_mk (@as_map F hF.1 x h) (TargetIsSet F x) := by {
  sorry;
}

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

theorem PowerClassExists (X : Class):
  ∃PX: Class,
    ∀z: Class, ∀_: Set z,
      z ∈ PX ↔ (z ⊂ X) := by {
  let px := Diff U (Dom ((RelInv E) ∩ (U ✕ (Diff U X))));
  let px_def := Diff_def U (Dom ((RelInv E) ∩ (U ✕ (Diff U X))));
  sorry;
}

noncomputable def PowerClass_mk (X : Class) : Class :=
  choose (PowerClassExists X)
noncomputable instance : HasPow Class where
  Pow := PowerClass_mk
noncomputable def PowerClass_def (X : Class):
  ∀z: Class, ∀_: Set z,
    z ∈ 𝒫 X ↔ (z ⊂ X) :=
  choose_spec (PowerClassExists X)
def isPowerClass (PX : Class) :=
  ∃(X: Class), ∀(Y: Class), ∀(_: Set Y), Y ∈ PX ↔ Y ⊂ X
class PowerClass (PX : Class) where
  isPowerClass: isPowerClass PX

theorem PowerClass_def'_is_PowerClass {X: Class}:
  isPowerClass (𝒫 X) := ⟨X, PowerClass_def X⟩

theorem UnivIsClosedPowerSet:
  U ＝ 𝒫 U := by {
  rw [AxiomExtensionality];
  intro z;
  apply Iff.intro;
  {
    intro h;
    rw [PowerClass_def U z (Set.mk₁ h)];
    exact AllSetSubsetU z;
  }
  {exact fun h => (Set.mk₁ h).2;}

}

