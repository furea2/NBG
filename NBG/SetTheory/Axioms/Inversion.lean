import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Product

open Classical

-- 6. AxiomInversion
axiom AxiomInversion :
  ∀X: Class, ∃Y: Class,
    ∀x y: Class, ∀_: Set x, ∀_: Set y,
      ((∃u: Class, ((u ＝ ＜x, y＞) ∧ u ∈ X)) ↔ (＜y, x＞) ∈ Y)

-- Todo..
theorem RelInvExists (R: Class) [hR: Relation R]:
  ∃RelInv_R: Class,
    ∀z: Class, (z ∈ RelInv_R)
      ↔ (∃x y: Class, ∃_: Set x, ∃_: Set y, ∃_:＜x,y＞ ∈ R,
        (z ＝ (＜y, x＞))) := by {
  let RelInv_R := choose (AxiomInversion R);
  have RelInv_R_def := choose_spec (AxiomInversion R);
  have rel_def := hR.1;
  exists RelInv_R;
  intro z;
  apply Iff.intro;
  {
    intro h;
    have := hR.1 z;
    -- rw [hR.1];
    sorry;
  }
  {
    intro ⟨x, y, hx, hy, hsub, heq⟩;
    have rel_def := (hR.1 z).2 ⟨y, ⟨x, ⟨hy, hx, heq⟩⟩⟩;

    sorry;
  }
}
noncomputable def RelInv (R: Class) [Relation R]:=
  choose (RelInvExists R)
noncomputable def RelInv_def (R: Class) [Relation R]:
  ∀z: Class, (z ∈ RelInv R)
    ↔ (∃x y: Class, ∃_: Set x, ∃_: Set y, ∃_:＜x,y＞ ∈ R,
        (z ＝ (＜y, x＞))) :=
  choose_spec (RelInvExists R)

theorem RelInvRelationIsRelation {R: Class} [hR: Relation R]:
  isRelation (RelInv R) := by {
  have rel_def := hR.1;
  intro z;
  have inv_def := RelInv_def R z;
  apply Iff.intro;
  {
    intro h;
    have ⟨y, x, hy, hx, _, heq⟩ := (inv_def.1 h);
    exists x, y, hx, hy;
  }
  {
    intro ⟨y, x, hy, hx, heq⟩;
    have h1 := (rel_def ＜x, y＞).2 ⟨x, ⟨y, ⟨hx, ⟨hy, ClassEq.refl _⟩⟩⟩⟩;
    exact (inv_def.2 ⟨x, ⟨y, ⟨hx, ⟨hy, h1, heq⟩⟩⟩⟩);
  }
}

theorem RelIffRelInRelInv (R: Class) [hR: Relation R]:
  (R ＝ @RelInv (RelInv R) ⟨RelInvRelationIsRelation⟩) := by {
  rw [AxiomExtensionality];
  intro z;
  have rel_inv_def := fun z => (@RelInvRelationIsRelation R hR z);
  have rel_inv_inv_def := fun z =>
    (@RelInvRelationIsRelation (RelInv R) ⟨rel_inv_def⟩ z);
  rw [rel_inv_inv_def, hR.1];
  exact Iff.rfl;
}

