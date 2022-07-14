import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Inversion

open Classical

-- 7. AxiomDomain
axiom AxiomDomain :
  ∀X: Class, ∃D: Class,
    ∀z: Class,
      (z∈D ↔ (∃x y: Class, ∃_: Set x, ∃_: Set y,
        ∃_:＜x, y＞ ∈ X, (z ＝ x)))

-- domain
noncomputable def Dom (X: Class): Class :=
  choose (AxiomDomain X)
noncomputable def Dom_def (X: Class):
  ∀z: Class,
    (z∈(Dom X) ↔ (∃x y: Class, ∃_: Set x, ∃_: Set y,
      ∃_:＜x, y＞ ∈ X, (z ＝ x))) :=
  choose_spec (AxiomDomain X)

-- rangle
noncomputable def Rng (X: Class) [Relation X]: Class :=
  choose (AxiomDomain (RelInv X))
noncomputable def Rng_def (X: Class) [Relation X]:
  ∀z: Class,
    (z∈(Rng X) ↔ (∃x y: Class, ∃_: Set x, ∃_: Set y,
      ∃_:＜x, y＞ ∈ X, (z ＝ y))) := by {
  intro z;
  have rng_def := choose_spec (AxiomDomain (RelInv X)) z;
  have rel_inv_def := RelInv_def X;
  apply Iff.intro;
  {
    intro h;
    have ⟨y,x,set_y,set_x,hin,heq⟩ := rng_def.1 h;
    have ⟨x1,y1,set_x1,set_y1,hin1,heq1⟩ := (rel_inv_def ＜y,x＞).1 hin;
    have heq2 := OrdPairEq.2 ⟨(OrdPairEq.1 heq1).2,(OrdPairEq.1 heq1).1⟩;
    have hin2 := ClassEqMenberImpMenber heq2 hin1;
    exists x,y,set_x,set_y,hin2;
  }
  {
    intro ⟨y,x,set_y,set_x,hin,heq⟩;
    apply rng_def.2;
    have hin1 := (rel_inv_def ＜x,y＞).2 ⟨y,x,set_y,set_x,hin,ClassEq.refl _⟩;
    exact ⟨x,y,set_x,set_y,hin1,heq⟩;
  }
}

