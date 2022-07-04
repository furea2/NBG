import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Product

open Classical

-- 6. AxiomInversion
axiom AxiomInversion :
  ∀X: Class, ∃Y: Class,
    ∀z: Class, (z ∈ Y)
      ↔ (∃x y: Class, ∃_: Set x, ∃_: Set y, ∃_:＜x,y＞ ∈ X,
        (z ＝ (＜y, x＞)))

-- theorem RelInvExists (R: Class):
--   ∃RelInv_R: Class,
--     ∀z: Class, (z ∈ RelInv_R)
--       ↔ (∃x y: Class, ∃_: Set x, ∃_: Set y, ∃_:＜x,y＞ ∈ R,
--         (z ＝ (＜y, x＞))) := AxiomInversion R
noncomputable def RelInv (R: Class): Class :=
  choose (AxiomInversion R)
noncomputable def RelInv_def (R: Class):
  ∀z: Class, (z ∈ RelInv R)
    ↔ (∃x y: Class, ∃_: Set x, ∃_: Set y, ∃_:＜x,y＞ ∈ R,
        (z ＝ (＜y, x＞))) :=
  choose_spec (AxiomInversion R)

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
  (R ＝ RelInv (RelInv R)) := by {
  rw [AxiomExtensionality];
  intro z;
  have rel_inv_def := fun z => (@RelInvRelationIsRelation R hR z);
  have rel_inv_inv_def := fun z =>
    (@RelInvRelationIsRelation (RelInv R) ⟨rel_inv_def⟩ z);
  rw [rel_inv_inv_def, hR.1];
  exact Iff.rfl;
}

theorem IsRelIffRelIffRelInRelInv (R: Class):
  isRelation R ↔ (R ＝ RelInv (RelInv R)) := by {
  apply Iff.intro;
  {exact fun h => @RelIffRelInRelInv R ⟨h⟩}
  {
    intro h;
    sorry;
  }
}

