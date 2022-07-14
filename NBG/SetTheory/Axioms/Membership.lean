import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Domain

open Classical

-- 8. AxiomMembership
axiom AxiomMembership :
  ∃E: Class, ∀z: Class,
    (z ∈ E ↔ ∃x y: Class, ∃_: Set x, ∃_: Set y,
      ∃_:x ∈ y,
        z ＝ ＜x, y＞)

-- class E
noncomputable def E: Class := choose AxiomMembership
noncomputable def E_def:
  ∀z: Class,
    (z ∈ E ↔ ∃x y: Class, ∃_: Set x, ∃_: Set y,
      ∃_:x ∈ y,
        z ＝ ＜x, y＞) :=
  choose_spec AxiomMembership

theorem EIsRelation:
  isRelation E := by {
  intro z h;
  have ⟨x,y,hx,hy,_,heq⟩ := (E_def z).1 h;
  exact ⟨x,y,hx,hy,heq⟩;
}

theorem DomEEqUniv : (Dom E) ＝ U := by {
  rw [AxiomExtensionality];
  intro z;
  rw [Dom_def];
  apply Iff.intro;
  {
    intro h;
    let h1 := choose_spec h;
    let h2 := choose_spec h1;
    let h3 := choose_spec h2;
    let h4 := choose_spec h3;
    let x := choose h;
    have set_x: Set x := choose h2;
    have heq: z ＝ x := choose_spec h4;
    exact ClassEqMenberImpMenber heq set_x.2;
  }
  {
    intro h;
    have set_z := Set.mk₂ h;
    let y := Singleton_mk z;
    have hy :=Singleton_def z;
    have set_y := Set.mk₂ hy.1;
    have z_in_y : z ∈ y := (hy.2 z).2 (ClassEq.refl _);
    have hin := (E_def ＜z,y＞).2 ⟨z,y,set_z,set_y,z_in_y,ClassEq.refl _⟩
    exists z,y,set_z,set_y,hin;
    exact ClassEq.refl _;
  }
}

-- Image type
theorem ImageClassExists (R X: Class.{u}) [hR: Relation R]:
  ∃Im: Class.{u}, ∀z: Class,
    ((z ∈ Im)
      ↔ (∃x y: Class, ∃_: Set y, ∃(hx:x ∈ X), ∃(_:(@OrdPair_mk x y (Set.mk₁ hx) _)∈ R),
        z ＝ y)) := by {
  have : Relation (R ∩ (X ✕ U)) :=
    ⟨fun z h => (hR.1 z) ((IntersectionClass_def R (X ✕ U) z).1 h).1⟩;
  let im := Rng (R ∩ (X ✕ U));
  let im_def := Rng_def (R ∩ (X ✕ U));
  have inter_def := IntersectionClass_def R (X ✕ U);
  have rel_def := hR.1;
  have prod_def := ProductClass_def X U;
  exists im;
  intro z;
  apply Iff.intro;
  {
    intro h;
    have ⟨x,y,set_x,set_y,hin,heq⟩ := (im_def z).1 h;
    have h1 := (inter_def ＜x, y＞).1 hin;
    have ⟨x2,y2,set_x2,set_y2,heq2⟩ := (rel_def ＜x, y＞) h1.1;
    have ⟨x3,y3,hx3,hy3,heq3⟩ := (prod_def ＜x, y＞).1 h1.2;
    have set_x3 := Set.mk₁ hx3;
    have set_y3 := Set.mk₁ hy3;
    rw [OrdPairEq] at heq2;
    rw [OrdPairEq] at heq3;
    exists x,y,set_y,ClassEqMenberImpMenber heq3.1 hx3;
    exists ClassEqMenberImpMenber (OrdPairEq.2 ⟨ClassEq.refl _,ClassEq.refl _⟩) h1.1;
  }
  {
    intro ⟨x,y,set_y,x_in_X,xy_in_R,heq⟩;
    have set_x := Set.mk₁ x_in_X;
    apply (im_def z).2;
    clear im_def;
    exists x,y,set_x,set_y;
    have h2 := (prod_def ＜x,y＞).2 ⟨x,y,x_in_X,set_y.2,(OrdPairEq.2 ⟨ClassEq.refl _,ClassEq.refl _⟩)⟩;
    have h3 := (inter_def ＜x,y＞).2 ⟨xy_in_R,h2⟩;
    exists h3;
  }
}
noncomputable def Im (R X: Class) [Relation R]: Class :=
  choose (ImageClassExists R X)
noncomputable def ImageClass_def (R X: Class.{u}) [Relation R]:
  ∀z: Class,
      ((z ∈ (Im R X))
        ↔ (∃x y: Class, ∃_: Set y, ∃(hx:x ∈ X), ∃(_:(@OrdPair_mk x y (Set.mk₁ hx) _)∈ R),
          z ＝ y)) :=
  choose_spec (ImageClassExists R X)

theorem PreImageClassExists (R X: Class) [Relation R]:
  ∃PreIm: Class, ∀z: Class,
    ((z ∈ PreIm)
      ↔ (∃x y: Class, ∃_: Set y, ∃(hx:x ∈ X), ∃(_:(@OrdPair_mk x y (Set.mk₁ hx) _) ∈ (RelInv R)),
        z ＝ y)) :=
  @ImageClassExists (RelInv R) X ⟨RelInvRelationIsRelation⟩


noncomputable def Apply (F x: Class) {h: x ∈ (Dom F)} : Class :=
  choose (choose_spec ((Dom_def F x).1 h))
noncomputable def Apply_def (F x: Class) {h: x ∈ (Dom F)} :=
  choose_spec ((Dom_def F x).1 h)
noncomputable def TargetIsSet (F x: Class) {h: x ∈ (Dom F)} : Set (@Apply F x h) :=
  choose (choose_spec (choose_spec (choose_spec ((Dom_def F x).1 h))))
noncomputable def SourceTargetPairIsIn (F x: Class) {h: x ∈ (Dom F)} :
  (@OrdPair_mk x (@Apply F x h) (Set.mk₁ h) (TargetIsSet F x)) ∈ F := by {
  have h1 := choose_spec ((Dom_def F x).1 h);
  have h2 := choose_spec h1;
  have h3 := choose_spec h2;
  have h4 := choose_spec h3;
  let u := choose ((Dom_def F x).1 h);
  let v := choose h1;
  have set_u : Set u := choose h2;
  have set_v : Set v := choose h3;
  have hin : ＜u,v＞ ∈ F := choose h4;
  have heq_x : x ＝ u := choose_spec h4;
  let y := @Apply F x h;
  have heq_y: y ＝ v := ClassEq.refl _;
  have set_x := Set.mk₁ h;
  have set_y := @TargetIsSet F x h;
  apply ClassEqMenberImpMenber _ hin;
  exact (@OrdPairEq x y u v set_x set_y set_u set_v).2 ⟨heq_x,heq_y⟩;
}
theorem ApplyFunctionUniqueTarget (F x x': Class) [set_x:Set x] [set_x':Set x']
    {hx: x ∈ (Dom F)} {hx': x' ∈ (Dom F)} [hF: Function F]:
      x ＝ x' →  @Apply F x hx ＝ @Apply F x' hx' := by {
  let y := @Apply F x hx;
  let y' := @Apply F x' hx';
  have set_y: Set y := @TargetIsSet F x hx;
  have set_y': Set y' := @TargetIsSet F x' hx';
  have F_def: ＜x, y＞ ∈ F → ＜x', y'＞ ∈ F
    → x ＝ x' → y ＝ y' :=
    hF.2 x x' y y' set_x set_x' set_y set_y';
  have hxy: ＜x, y＞ ∈ F := @SourceTargetPairIsIn F x hx;
  have hxy': ＜x', y'＞ ∈ F := @SourceTargetPairIsIn F x' hx';
  exact fun h => F_def hxy hxy' h;
}

-- define useful notation
noncomputable def as_map (F x: Class) [Relation F] {h: x ∈ Dom F}: Class := by
exact (@Apply F x h)
notation F"【"x"】" => as_map F x

/-- The brige theorem of image and function, namely f[ X ] = {f(x)}. -/
theorem SingleSetFunctionImageIsSingleton (F x: Class) [hx: Set x] {h: x ∈ (Dom F)} [hF: Function F]:
  Im F x ＝ @Singleton_mk (@as_map F x hF.1 h) (TargetIsSet F x) := by {
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
  have px_def := Diff_def U (Dom ((RelInv E) ∩ (U ✕ (Diff U X))));
  have dom_def := Dom_def ((RelInv E) ∩ (U ✕ (Diff U X)));
  have inter_def := IntersectionClass_def (RelInv E) (U ✕ (Diff U X));
  have rel_inv_def := RelInv_def E;
  have prod_def := ProductClass_def U (Diff U X);
  have diff_def := Diff_def U X;
  have E_def := E_def;
  exists px;
  intro z set_z;
  apply Iff.intro;
  {
    intro h u hu;
    have set_u :=  (Set.mk₁ hu);
    have h1 := ((px_def z).1 h);
    have h2 := (
      ImpIffNotImpNot.1 (
        NotExistsImpForall (
          NotExistsImpForall (
            NotExistsImpForall (
              NotExistsImpForall (
                NotExistsImpForall (
                  (IffIffNotIffNot.1 (dom_def z)).2 h1.2) z) u) set_z) set_u)) (IffNotNot.1 ((ClassEq.refl _))));
    have h3 := NotAndIffNotOrNot.1 ((IffIffNotIffNot.1 (inter_def ＜z,u＞)).2 h2);
    cases h3;
    case mp.inl h3 => {
      have h4 := ImpIffNotImpNot.1 (
        ExistsIffNotForall.1 (
          ExistsIffNotForall.1 (
            ExistsIffNotForall.1 (
              ExistsIffNotForall.1 (
                ExistsIffNotForall.1 (
                  (IffIffNotIffNot.1 (rel_inv_def ＜z,u＞)).2 h3) u) z) set_u) set_z)) (IffNotNot.symm.2 (ClassEq.refl _));
      have := (E_def ＜u,z＞).2;
      have h5 := (
        ExistsIffNotForall.1 (
          ExistsIffNotForall.1 (
            ExistsIffNotForall.1 (
              ExistsIffNotForall.1 (
                ExistsIffNotForall.1 (
                  (IffIffNotIffNot.1 (E_def ＜u,z＞)).2 h4) u) z) set_u) set_z) hu);
      exact False.elim (h5 (ClassEq.refl _));
    }
    case mp.inr h3 => {
      have h4 := (@ImpIffNotImpNot (u ∈ Diff U X) (¬＜z,u＞ ＝ ＜z,u＞)).1 (
        ExistsIffNotForall.1 (
          ExistsIffNotForall.1 (
            ExistsIffNotForall.1 (
              ExistsIffNotForall.1 (
                (IffIffNotIffNot.1 (prod_def ＜z,u＞)).2 h3) z) u) set_z.2)) (IffNotNot.symm.2 (ClassEq.refl _));
      have h5 := NotAndIffNotOrNot.1 ((IffIffNotIffNot.1 (diff_def u)).2 h4);
      cases h5;
      case inl h5 => {exact False.elim (h5 set_u.2);}
      case inr h5 => {exact IffNotNot.2 h5;}
    }
  }
  {
    intro h;
    apply (px_def z).2;
    apply And.intro;
    {exact set_z.2;}
    {
      intro hn;
      
      -- have := (dom_def z).1 hn;
      have ⟨z1,u,set_z1,set_u,hin1,heq1⟩ := (dom_def z).1 hn;
      have h1 := (inter_def ＜z1,u＞).1 hin1;
      have ⟨u2,z2,set_u2,set_z2,hin2,heq2⟩ := (rel_inv_def ＜z1,u＞).1 h1.1;
      have ⟨u3,z3,hu3,hz3,hin3,heq3⟩ := (E_def ＜u2,z2＞).1 hin2;

      have ⟨z4,u4,hz4,hu4,heq4⟩ := (prod_def ＜z1,u＞).1 h1.2;
      have h3 := (diff_def u4).1 hu4;
      rw [OrdPairEq] at heq2;
      rw [OrdPairEq] at heq3;
      have set_z4 := Set.mk₂ hz4;
      have set_u4 := Set.mk₁ hu4;
      rw [OrdPairEq] at heq4;
      -- have heq5 := (AxiomExtensionality z z4).1 (ClassEq.trans (OrdPairEq.1 heq2).1 (OrdPairEq.1 heq'').2);
      -- have heq''''' := ClassEq.trans (ClassEq.trans (ClassEq.symm (OrdPairEq.1 heq''').2) (OrdPairEq.1 heq').2) (OrdPairEq.1 heq'').1;
      -- have := (AxiomExtensionality z z2) ;
      have u_in_z : u ∈ X := by {
        apply (h u);
        apply ((AxiomExtensionality z z3).1 (ClassEq.trans (ClassEq.trans heq1 heq2.1) heq3.2) u).2;
        apply ClassEqMenberImpMenber (ClassEq.trans heq2.2 heq3.1) hin3;
      }
      have u_not_in_z : ¬ u ∈ X := @RewiteClass (fun u => ¬ u ∈ X) u u4 ⟨heq4.2,h3.2⟩;
      contradiction;
    }
  }
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

