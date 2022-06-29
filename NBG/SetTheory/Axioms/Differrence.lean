import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Universe

open Classical

-- 3. AxiomDifferrence
axiom AxiomDifferrence :
  ∀X Y: Class, ∃Z: Class,
    ∀u: Class, (u∈Z ↔ (u ∈ X ∧ u ∉ Y))
noncomputable def Diff (X Y: Class) := choose (AxiomDifferrence X Y)
noncomputable def DiffDif (X Y: Class) := choose_spec (AxiomDifferrence X Y)
noncomputable instance : HasDiff Class where
  Diff := Diff

noncomputable def Intersection (X Y: Class) :=
  X ＼ (X ＼ Y)
noncomputable instance : HasInter Class where
  Inter := Intersection
noncomputable def Union (X Y: Class) :=
  U ＼ ((U ＼ X) ∩ (U ＼ Y))
noncomputable instance : HasUnion Class where
  Union := Union
noncomputable def EmptyClass : Class :=
  U ＼ U
noncomputable def EmptyDef := choose_spec (AxiomDifferrence U U)
notation " ø " => EmptyClass
noncomputable def SymmDiff (X Y: Class) :=
  (X ∪ Y) ＼ (X ∩ Y)
infix:50 " △ " => SymmDiff

-- intersection

theorem IntersectionIntro (X Y: Class) :
  ∀z: Class, (z ∈ (X ∩ Y)) ↔ (z ∈ X) ∧ (z ∈ Y) := sorry

-- union
theorem UnionIntro (X Y: Class) :
  ∀z: Class, (z ∈ (X ∪ Y)) ↔ (z ∈ X) ∨ (z ∈ Y) := sorry

def isEmptySet (E : Class) := ∀(z : Class), ¬ z ∈ E
theorem EmptyClassIntro :
  ∀z: Class, ¬ z ∈ ø := by {
  intro z h;
  have := ((DiffDif U U) z).1 h;
  exact this.right this.left;
}

-- symmdiff
theorem SymmDiffIntro (X Y: Class) :
  ∀z: Class, (z ∈ (X △ Y)) ↔
    (z ∈ (X ＼ Y)) ∧ (z ∈ (Y ＼ X)) := sorry


theorem EmptyHasNoClass : ∀(X : Class), ¬(X ∈ ø) := by {
  intro X h;
  have emp_def := choose_spec (AxiomDifferrence U U);
  have hXU: ¬ X ∈ U := ((emp_def X).1 h).right;
  have hXU2 := AllSetInU.1 ⟨ø, h⟩;
  contradiction;
}

theorem UniqueEmptySet :
  isUnique (fun E : Class => ∀(z : Class), ¬ z ∈ E) := by {
  intro E E' hE hE';
  apply (AxiomExtensionality E E').2;
  intro z;
  apply Iff.intro;
  {
    intro h;
    apply False.elim;
    exact (hE z) h;
  }
  {
    intro h;
    apply False.elim;
    exact (hE' z) h;
  }
}

