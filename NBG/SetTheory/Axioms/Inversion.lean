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

theorem RelInvRelationIsRelation {R: Class} [Relation R]:
  isRelation (RelInv R) := by {
  intro z h;
  have ⟨y, x, hy, hx, _, heq⟩ := ((RelInv_def R z).1 h);
  exists x, y, hx, hy;
}

-- theorem RelInvRelationIsRelation {R: Class} [hR: Relation R]:
--   isRelation (RelInv R) := by {
--   have rel_def := hR.1;
--   intro z;
--   have inv_def := RelInv_def R z;
--   apply Iff.intro;
--   {
--     intro h;
--     have ⟨y, x, hy, hx, _, heq⟩ := (inv_def.1 h);
--     exists x, y, hx, hy;
--   }
--   {
--     intro ⟨y, x, hy, hx, heq⟩;
--     have h1 := (rel_def ＜x, y＞).2 ⟨x, ⟨y, ⟨hx, ⟨hy, ClassEq.refl _⟩⟩⟩⟩;
--     exact (inv_def.2 ⟨x, ⟨y, ⟨hx, ⟨hy, h1, heq⟩⟩⟩⟩);
--   }
-- }

theorem RelIffRelInRelInv (R: Class) [hR: Relation R]:
  (R ＝ RelInv (RelInv R)) := by {
  rw [AxiomExtensionality];
  intro z;
  have rel_def := hR.1;
  have rel_inv_def := RelInv_def R;
  have rel_inv_inv_def := RelInv_def (RelInv R);
  apply Iff.intro;
  {
    intro h;
    rw [rel_inv_inv_def];
    have ⟨x, y, hx, hy, heq⟩ := rel_def z h;
    have hin := ClassEqMenberImpMenber ⟨ClassEq.symm heq,h⟩;
    have hin' := (rel_inv_def ＜y, x＞).2 ⟨x,y,hx,hy,hin,ClassEq.refl _⟩;
    exact ⟨y,x,hy,hx,hin',heq⟩;
  }
  {
    intro h;
    have ⟨y, x, hy, hx, hin, heq⟩ := ((rel_inv_inv_def z).1 h);
    have ⟨x', y', hx', hy', hin', heq'⟩ := ((rel_inv_def ＜y,x＞).1 hin);
    have heq'' := OrdPairEq.2 ⟨(OrdPairEq.1 heq').2,(OrdPairEq.1 heq').1⟩;
    exact ClassEqMenberImpMenber ⟨ClassEq.trans heq heq'',hin'⟩;
  }
}

-- theorem IsRelIffRelIffRelInRelInv (R: Class):
--   isRelation R ↔ (R ＝ RelInv (RelInv R)) := by {
--   apply Iff.intro;
--   {exact fun h => @RelIffRelInRelInv R ⟨h⟩}
--   {
--     intro h;
--     sorry;
--   }
-- }

