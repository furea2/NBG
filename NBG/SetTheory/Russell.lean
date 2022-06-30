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
  have ⟨Y, hY⟩ := h;
  have hUU := AllSetInU.1 ⟨Y, hY⟩;
  let U' := @Singleton U ⟨⟨Y, hY⟩, hUU⟩;
  have U'_def := @SingletonIntro U ⟨⟨Y, hY⟩, hUU⟩;
  have hU' := (U'_def U).2 (ClassEq.refl U);
  by_cases hE : U'＝ø;
  {
    rw [AxiomExtensionality] at hE;
    rw [hE] at hU';
    have := (EmptyDef U).1 hU';
    exact this.2 this.1;
  }
  {
    have U_def := choose_spec AxiomUniverse;
    have ⟨B', hB'⟩ := (U_def U').1 (@Singleton_def U ⟨⟨Y, hY⟩, hUU⟩).1;
    have ⟨B, ⟨hB1, hB2⟩⟩ := AxiomFoundation U' (AllSetInU.1 ⟨B', hB'⟩) hE;
    rw [U'_def, AxiomExtensionality] at hB1;
    have : ∀z: Class, z∈ U → ¬ z ∈ U' := by {
      intro z hz;
      rw [←hB1] at hz;
      exact (hB2 z) hz;
    }
    exact (this U hUU) hU';
  }
}

