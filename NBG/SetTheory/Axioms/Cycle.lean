import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Membership

open Classical

-- 9. AxiomCycle
axiom AxiomCycle :
  ∀X: Class, ∃Y: Class, ∀z: Class,
    (z ∈ Y ↔ ∃u v w: Class,
      ∃_: Set u, ∃_: Set v, ∃_: Set w,
        ∃_:＜u,v,w＞ ∈ X,
          z ＝ ＜w,u,v＞)

theorem LeftCycleClassExists:
  ∀X: Class, ∃Y: Class, ∀z: Class,
    (z ∈ Y ↔ ∃u v w: Class,
      ∃_: Set u, ∃_: Set v, ∃_: Set w,
        ∃_:＜u,v,w＞ ∈ X,
          z ＝ ＜v,w,u＞) := by {
  intro X;
  let y1 := choose (AxiomCycle X);
  have y1_def := choose_spec (AxiomCycle X);
  let y2 := choose (AxiomCycle y1);
  let y2_def := choose_spec (AxiomCycle y1);
  exists y2;
  intro z;
  apply Iff.intro;
  {
    intro h;
    have ⟨w,u,v,set_w,set_u,set_v,h_wuv_in,h_vwu_eq⟩ :=
      (y2_def z).1 h;
    have ⟨u',v',w',set_u',set_v',set_w',h_uvw'_in,h_wuv_eq'⟩ :=
      (y1_def ＜w,u,v＞).1 h_wuv_in;
    exists u',v',w',set_u',set_v',set_w',h_uvw'_in;
    apply ClassEq.trans h_vwu_eq;
    rw [OrdTripleEq] at h_wuv_eq';
    apply OrdTripleEq.2;
    have := h_wuv_eq'.2.2;
    exact ⟨h_wuv_eq'.2.2,h_wuv_eq'.1,h_wuv_eq'.2.1⟩;
  }
  {
    intro ⟨v,w,u,set_v,set_w,set_u,h_vwu_in,h_wuv_eq⟩;
    rw [y2_def];
    have heq : ＜u,v,w＞ ＝ ＜u,v,w＞ := OrdTripleEq.2 ⟨ClassEq.refl _,ClassEq.refl _,ClassEq.refl _⟩;
    have := (y1_def ＜u,v,w＞).2 ⟨v,w,u,set_v,set_w,set_u,h_vwu_in,heq⟩;
    exact ⟨u,v,w,set_u,set_v,set_w,this,h_wuv_eq⟩;
  }
}


noncomputable def RightCycleClass (X: Class): Class :=
  choose (AxiomCycle X)
noncomputable def RightCycleClass_mk (X: Class) :=
  choose_spec (AxiomCycle X)
noncomputable def LeftCycleClass (X: Class): Class :=
  choose (LeftCycleClassExists X)
noncomputable def LeftCycleClass_mk (X: Class) :=
  choose_spec (LeftCycleClassExists X)

notation " ↻ " X => RightCycleClass X
notation " ↺ " X => LeftCycleClass X
