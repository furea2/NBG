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
  intro ⟨Y, hY⟩;
  let set_U : Set U := Set.mk₁ hY;
  have U'_def : ∀u: Class, u ∈ (Singleton_mk U) ↔ u ＝ U := (Singleton_def U).2;
  have hU' : U ∈ (Singleton_mk U) := (U'_def U).2 (ClassEq.refl U);
  by_cases hE : (Singleton_mk U) ＝ ø;
  {
    rw [AxiomExtensionality] at hE;
    rw [hE] at hU';
    have := (EmptyDef U).1 hU';
    exact this.2 this.1;
  }
  {
    have hUU := set_U.2;
    have : ∀z: Class, z∈ U → ¬ z ∈ (Singleton_mk U) := by {
      intro z hz;
      have U'_in_U : (Singleton_mk U) ∈ U :=
        sorry;
        -- (Singleton_def U).2.2 (Singleton_mk U);
      have ⟨B, ⟨hB1, hB2⟩⟩ := AxiomFoundation (Singleton_mk U) U'_in_U hE;
      rw [U'_def, AxiomExtensionality] at hB1;
      rw [←hB1] at hz;
      exact (hB2 z) hz;
    }
    exact (this U hUU) hU';
  }
}

