import NBG.SetTheory.Axioms.Basic

open Classical


-- subset function
theorem SubsetInductiveClassOppositeExists:
  ∃T: Class, ∀u:Class,
    (u ∈ T ↔ ∃x y z: Class, ∃_: Set x, ∃_: Set y, ∃_: Set z,
      ∃_: z ∈ x, ∃_: z ∉ y,
        u ＝ ＜x, y, z＞) := by {
  let t := (↺ (E ✕ U)) ∩ (↻ ((U₂ ＼ (RelInv E)) ✕ U));
  have t_def := IntersectionClass_def (↺ (E ✕ U)) (↻ ((U₂ ＼ (RelInv E)) ✕ U));
  have tl_def1 := LeftCycleClass_def (E ✕ U);
  have tl_def2 := ProductClass_def E U;
  have tr_def1 := RightCycleClass_def ((U₂ ＼ (RelInv E)) ✕ U);
  have tr_def2 := ProductClass_def (U₂ ＼ (RelInv E)) U;
  have tr_def3 := Diff_def U₂ (RelInv E);
  have tr_def4 := RelInv_def E;
  have u2_def := ProductClass_def U U;
  have E_def := E_def;
  exists t;
  intro u;
  rw [t_def];
  apply Iff.intro;
  {
    intro h;
    have ⟨z,x,y,set_z,set_x,set_y,hin,heq⟩ := (tl_def1 u).1 h.1;
    exists x,y,z,set_x,set_y,set_z;
    have z_in_x: z ∈ x := by {
      have ⟨e,y',e_in_E,hy',heq'⟩ := (tl_def2 ＜z,x,y＞).1 hin;
      have _ := Set.mk₁ e_in_E;
      have _ := Set.mk₁ hy';
      have ⟨z'',x'',set_z'', set_x'',z_in_x'',heq''⟩ := ((E_def e).1 e_in_E);
      have _ := OrdPair_is_Set z x;
      have zz_xx := OrdPairEq.1 (ClassEq.trans (OrdPairEq.1 heq').1 heq'');
      have := (((AxiomExtensionality x x'').1 zz_xx.2) z'').2 z_in_x'';
      exact ClassEqMenberImpMenber zz_xx.1 this;
    }
    have ⟨y',z',x',set_y',set_z',set_x',hin',heq'⟩ := (tr_def1 u).1 h.2;
    have z_not_in_y: z ∉ y := by {
      intro z_in_y;
      have ⟨e,x1,he,x1_in_U,yzx_eq_ex1⟩ := (tr_def2 ＜y',z',x'＞).1 hin';
      have he2 := (tr_def3 e).1 he;
      have ⟨y1,z1,hy1,hz1,e_eq_y1z1⟩ := (u2_def e).1 he2.1;
      have set_z1 := Set.mk₁ hz1;
      have set_y1 := Set.mk₁ hy1;
      have hn_z1y1 :=  ImpIffNotImpNot.1 (
        NotExistsImpForall (
          NotExistsImpForall (
            NotExistsImpForall (
              NotExistsImpForall (
                NotExistsImpForall (
        (IffIffNotIffNot.1 (tr_def4 e)).2 he2.2) z1) y1) set_z1) set_y1)) (IffNotNot.1 e_eq_y1z1);
      have zy_eq_z1y1 : ＜z,y＞ ＝ ＜z1,y1＞ := by {
        have heq_xyz:= OrdTripleEq.1 (ClassEq.trans (ClassEq.symm heq) heq');
        have _ := Set.mk₁ he;
        have _ := OrdPair_is_Set y' z';
        have _ := Set.mk₂ x1_in_U;
        have heq_yy_zz := OrdPairEq.1 (ClassEq.trans (OrdPairEq.1 yzx_eq_ex1).1 e_eq_y1z1);
        have z_eq_z1:= ClassEq.trans heq_xyz.2.2 heq_yy_zz.2;
        have y_eq_y1:= ClassEq.trans heq_xyz.2.1 heq_yy_zz.1;
        exact OrdPairEq.2 ⟨z_eq_z1,y_eq_y1⟩;
      };
      have h_z1y1 := (E_def ＜z1,y1＞).2 ⟨z,y,set_z,set_y,z_in_y,ClassEq.symm zy_eq_z1y1⟩;
      contradiction;
    }
    exists z_in_x,z_not_in_y;
  }
  {
    intro ⟨x,y,z,set_x,set_y,set_z,z_in_x,z_not_in_y,u_eq_xyz⟩;
    apply And.intro;
    {
      apply (tl_def1 u).2;
      have zx_in_E := (E_def ＜z,x＞).2 ⟨z,x,set_z,set_x,z_in_x,ClassEq.refl _⟩
      have hzxy := (tl_def2 ＜z,x,y＞).2 ⟨＜z,x＞,y,zx_in_E,set_y.2,ClassEq.refl _⟩;
      exists z,x,y,set_z,set_x,set_y,hzxy;
    }
    {
      apply (tr_def1 u).2;
      exists y,z,x,set_y,set_z,set_x;
      have yz_in_u2 := (u2_def ＜y,z＞).2 ⟨y,z,set_y.2,set_z.2,ClassEq.refl _⟩;
      have yz_not_in_relinv_u2: ¬ (＜y,z＞ ∈ RelInv E) := by {
        intro h;
        have ⟨z1,y1,set_z1,set_y1,z1y1_in_E,yz_eqy1z1⟩:= (tr_def4 ＜y,z＞).1 h;
        have ⟨z2,y2,set_z2,set_y2,z2_in_y2,heq_zz_yy⟩:= (E_def ＜z1,y1＞).1 z1y1_in_E;
        have yy_zz1 := OrdPairEq.1 yz_eqy1z1;
        have zz_yy2 := OrdPairEq.1 heq_zz_yy;
        have := ((AxiomExtensionality y y2).1 (ClassEq.trans yy_zz1.1 zz_yy2.2) z).2 (
          ClassEqMenberImpMenber (ClassEq.trans yy_zz1.2 zz_yy2.1) z2_in_y2);
        contradiction;
      }
      have h_yz_in := (tr_def3 ＜y,z＞).2 ⟨yz_in_u2,yz_not_in_relinv_u2⟩;
      exists (tr_def2 ＜y,z,x＞).2 ⟨＜y,z＞,x,h_yz_in,set_x.2,ClassEq.refl _⟩;
    }
  }
}

private noncomputable def T : Class :=
  choose SubsetInductiveClassOppositeExists
private noncomputable def T_def :=
  choose_spec SubsetInductiveClassOppositeExists

theorem SubsetInductiveClassExists:
  ∃S: Class, ∀z:Class,
    (z ∈ S ↔ ∃x y: Class, ∃hx: Set x, ∃hy: Set y,
      ∃_: x ⊂ y,
        z ＝ ＜x, y＞) := by {
  let s := U₂ ＼ (Dom T);
  have s_def := Diff_def U₂ (Dom T);
  have dom_def := Dom_def T;
  have t_def := T_def;
  have u2_def := ProductClass_def U U;

  exists s;
  intro u;
  rw [s_def];
  apply Iff.intro;
  {
    intro h;
    have ⟨x,y,hx,hy,hu⟩ := (u2_def u).1 h.1;
    have set_x := (Set.mk₂ hx);
    have set_y := (Set.mk₂ hy);
    have _:= (OrdPair_is_Set x y);
    have set_u: Set u := Set.mk₁ h.1;
    have : x ⊂ y := by {
      have ht := ExistsIffNotForall.1 ((IffIffNotIffNot.1 (dom_def u)).2 h.2);
      clear s_def u2_def dom_def;
      intro v hv;
      by_cases hz': (∃z: Class, z ∈ x ∧ z ∉ y);
      {
        let z := choose hz';
        have hz: z ∈ x ∧ z ∉ y := choose_spec hz';
        have set_z := Set.mk₁ hz.1
        have ht1 := ht z;
        have uz_eq_xyz: ＜u,z＞ ＝ ＜x,y,z＞ := OrdPairEq.2 ⟨hu , ClassEq.refl z⟩;
        have ez_in_T: ∃_:Set z, ＜u,z＞ ∈ T :=
          ⟨set_z, (t_def ＜u,z＞).2 ⟨x,y,z,set_x,set_y,set_z,hz.1,hz.2,uz_eq_xyz⟩⟩;
        clear t_def;
        -- contradiction;
        sorry;
      }
      {
        cases NotAndIffNotOrNot.1 ((ExistsIffNotForall.1 hz') v);
        case inr.inl hvy => {contradiction;}
        case inr.inr hvy => {exact (IffNotNot.2 hvy);}
      }
    }
    exists x,y,set_x,set_y,this;
  }
  {
    intro ⟨x,y,set_x,set_y,x_subset_y,hu⟩;
    apply And.intro;
    {exact (u2_def u).2 ⟨x,y,set_x.2,set_y.2,hu⟩;}
    {
      intro hn;
      have set_u: Set u := Set.mk₁ hn;
      have ⟨u',z,set_u',set_z,uz_in_T,huu'⟩:= (dom_def u).1 hn;
      have ⟨x',y',z',set_x',set_y',set_z',z_in_x',z_not_in_y',heq'⟩ :=
        (t_def ＜u',z＞).1 uz_in_T;
      have set_xy' := (OrdPair_is_Set x' y')
      have heq'' :=
        (@OrdPairEq u' z ＜x',y'＞ z' set_u' set_z set_xy' set_z').1 heq';
      have heq''' :=
        OrdPairEq.1 (ClassEq.trans (ClassEq.trans (ClassEq.symm hu) huu') heq''.1);
      have :=
        (((AxiomExtensionality y y').1 heq'''.2) z').1 ((x_subset_y z') ((((AxiomExtensionality x x').1 heq'''.1) z').2 z_in_x'));
      contradiction;
    }
  }
}

noncomputable def S : Class :=
  choose SubsetInductiveClassExists
noncomputable def S_def:
  ∀z:Class,
    (z ∈ S ↔ ∃x y: Class, ∃_: Set x, ∃_: Set y,
      ∃_: x ⊂ y,
        z ＝ ＜x, y＞) :=
  choose_spec SubsetInductiveClassExists

theorem SubsetPairAreInS {x y: Class} [hx: Set x] [hy: Set y]:
  x ⊂ y → ＜x, y＞ ∈ S :=
  fun h => (S_def ＜x,y＞).2 ⟨x, y, hx, hy, h, ClassEq.refl _⟩

-- identity function
theorem IdentityClassExists:
  ∃Id: Class, ∀z:Class,
    (z ∈ Id ↔ ∃x: Class, ∃_: Set x, z ＝ ＜x, x＞) := by {
  let id := S ∩ (RelInv S);
  have id_def := IntersectionClass_def S (RelInv S);
  have relinv_def := RelInv_def S;
  have s_def := S_def;

  exists id;
  intro z;
  rw [id_def, relinv_def, s_def];
  apply Iff.intro;
  {
    intro ⟨⟨x,y,set_x,set_y,hxy,hz1⟩,⟨x',y',set_x',set_y',hxy',hz2⟩⟩;
    have ⟨x'',y'',set_x'',set_y'',hxy'',hz3⟩ := (s_def ＜x',y'＞).1 hxy';
    have heq := OrdPairEq.1 (ClassEq.trans (ClassEq.symm hz1) hz2);
    have heq' := OrdPairEq.1 hz3;
    have hyx : y ⊂ x := by {
      intro z;
      have hx1 := ((AxiomExtensionality x y').1 heq.1 z).2;
      have hx2:= ((AxiomExtensionality y' y'').1 heq'.2 z).2;
      have hy1 := ((AxiomExtensionality y x').1 heq.2 z).1;
      have hy2:= ((AxiomExtensionality x' x'').1 heq'.1 z).1;
      have := (hxy'' z);
      exact fun h => hx1 (hx2 ((hxy'' z) (hy2 (hy1 h))));
    };
    clear id_def relinv_def s_def id hxy' hxy'' hz2 hz3 heq heq';
    exists x, set_x;
    have := ClassSubsetSymmImplyEq hyx hxy;
    have := (@OrdPairEq x y x x set_x set_y set_x set_x).2 ⟨ClassEq.refl _, this⟩;
    exact ClassEq.trans hz1 this;
  }
  {
    intro ⟨x,hx,hz⟩;
    have hxxS := (s_def ＜x,x＞).2 ⟨x,x,hx,hx,ClassSubset.refl _,ClassEq.refl _⟩;
    exact ⟨⟨x,x,hx,hx,ClassSubset.refl _, hz⟩,⟨x,x,hx,hx,hxxS,hz⟩⟩;
  }
}

noncomputable def IdClass : Class :=
  choose IdentityClassExists
noncomputable def IdClass_def:
  ∀z:Class,
    (z ∈ IdClass ↔ ∃x: Class, ∃_: Set x, z ＝ ＜x, x＞) :=
  choose_spec IdentityClassExists

theorem AllIdSetIsInId (x: Class) [hx: Set x]:
  ＜x, x＞ ∈ IdClass :=
(IdClass_def ＜x, x＞).2 ⟨x, ⟨hx, ClassEq.refl _⟩⟩

theorem IdClassIsRelation:
  isRelation IdClass := sorry

