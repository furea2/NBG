import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Basic

open Classical

def isNotSelfIncluided (X : Class) : Prop := (X ∉ X)

theorem Russel':
  (∃A : Class, ∀x : Class,
    (x ∈ A) ↔ (isNotSelfIncluided x)) → False:= by {
  intro ⟨A, h⟩;
  have := h A;
  by_cases hA : A∈A;
  {have := this.1 hA; contradiction}
  {have := this.2 hA; contradiction}
}

theorem Russel (R : Class):
  (∀x: Class,
    (x∈R) ↔ ((isSet x) ∧ (isNotSelfIncluided x)))
    → (isProper R) := by {
  intro R_def;
  have hR := R_def R;
  by_cases h1 : R ∈ R;
  {
    apply False.elim _;
    have : R ∉ R := (hR.1 h1).2;
    contradiction;
  }
  {
    by_cases h2 : isSet R;
    {
      apply False.elim _;
      have : R ∈ R := (hR.2 ⟨h2,h1⟩);
      contradiction;
    }
    {exact h2;}
  }
}

theorem UnivIsProper:
  isProper U := by {
  intro h;
  let U_set : SetType := SetType.mk₁ U h;
  have U'_def : ∀u: Class, u ∈ {U_set}c ↔ u ＝ U := (Singleton_def U_set);
  have hU' : U ∈ {U_set}c := (U'_def U).2 (ClassEq.refl U);
  by_cases hE : {U_set}c ＝ ø;
  {
    rw [AxiomExtensionality] at hE;
    rw [hE] at hU';
    have := (EmptyDef U).1 hU';
    exact this.2 this.1;
  }
  {
    have hUU := AllSetInU.1 h;
    have : ∀z: Class, z∈ U → ¬ z ∈ {U_set}c := by {
      intro z hz;
      have U'_in_U : {U_set}c ∈ U := {U_set}s.2.2;
      have ⟨B, ⟨hB1, hB2⟩⟩ := AxiomFoundation {U_set}c U'_in_U hE;
      rw [U'_def, AxiomExtensionality] at hB1;
      rw [←hB1] at hz;
      exact (hB2 z) hz;
    }
    exact (this U hUU) hU';
  }
}

