import NBG.SetTheory.Axioms.Basic

open Classical


-- subset function
theorem SubsetInductiveClassOppositeExists:
  ∃T: Class, ∀z:Class, z ∈ T ↔ z ＝ z
    -- (z ∈ T ↔ ∃x y z: Class, ∃_: Set x, ∃_: Set y, ∃_: Set z,
    --   ∃_: z ∈ x, ∃_: z ∉ y,
    --     z ＝ ＜x, y, z＞) := by {
:= by {
  -- let t := (↺ (E ✕ U)) ∩ (↺ ((U₂ ＼ (RelInv E)) ✕ U));
  -- have t_def := IntersectionClass_def (↺ (E ✕ U)) (↺ ((U₂ ＼ (RelInv E)) ✕ U));
  -- have tl_def := RightCycleClass_mk (E ✕ U);
  -- have tr_def1 := IntersectionClass_def ((U₂ ＼ (RelInv E)) ✕ U);
  -- have tr_def2 := ProductClass_def (U₂ ＼ (RelInv E)) U;
  -- have tr_def3 := Diff_def U₂ (RelInv E);
  -- have tr_def4 := RelInv_def E;
  -- exists t;
  -- intro z;

  -- rw [t_def];
  sorry;
}

private noncomputable def T : Class :=
  choose SubsetInductiveClassOppositeExists
private noncomputable def T_def :=
  choose_spec SubsetInductiveClassOppositeExists


theorem SubsetInductiveClassExists:
  ∃S: Class, ∀z:Class,
    (z ∈ S ↔ ∃x y: Class, ∃_: Set x, ∃_: Set y,
      ∃_: x ⊂ y,
        z ＝ ＜x, y＞) := by {
  let s := (U₂ ＼ (Dom T));
  -- have t_def := IntersectionClass_def (↺ (E ✕ U)) (↺ ((U₂ ＼ (RelInv E)) ✕ U));
  sorry;
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
theorem IdentityFunctionExists:
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
  choose IdentityFunctionExists
noncomputable def IdClass_def:
  ∀z:Class,
    (z ∈ IdClass ↔ ∃x: Class, ∃_: Set x, z ＝ ＜x, x＞) :=
  choose_spec IdentityFunctionExists

theorem AllIdSetIsInId (x: Class) [hx: Set x]:
  ＜x, x＞ ∈ IdClass :=
(IdClass_def ＜x, x＞).2 ⟨x, ⟨hx, ClassEq.refl _⟩⟩



