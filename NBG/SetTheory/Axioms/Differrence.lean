import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Universe

open Classical

-- 3. AxiomDifferrence
axiom AxiomDifferrence :
  ∀X Y: Class, ∃Z: Class,
    ∀u: Class, (u∈Z ↔ (u ∈ X ∧ u ∉ Y))
noncomputable def Diff (X Y: Class) := choose (AxiomDifferrence X Y)
infix:50 " ＼ " => Diff

noncomputable def Intersection (X Y: Class) :=
  X ＼ (X ＼ Y)
infix:50 " ∩ " => Intersection
noncomputable def Union (X Y: Class) :=
  U ＼ ((U ＼ X) ∩ (U ＼ Y))
infix:50 " ∪ " => Union
noncomputable def EmptyClass :=
  U ＼ U
notation " ∅ " => EmptyClass
noncomputable def SymmDiff (X Y: Class) :=
  (X ∪ Y) ＼ (X ∩ Y)
infix:50 " △ " => SymmDiff

def isEmptySet (E : Class) := ∀(z : Class), ¬ z ∈ E

theorem EmptyHasNoClass : ∀(X : Class), ¬(X ∈ ∅) := by {
  intro X h;
  have emp_def := choose_spec (AxiomDifferrence U U);
  have hXU: ¬ X ∈ U := ((emp_def X).1 h).right;
  have hXU2 := AllSetInU ⟨∅, h⟩;
  contradiction;
}

theorem UniqueEmptySet :
  isUnique (fun E : Class => ∀(z : Class), ¬ z ∈ E) := by {
  intro E E' hE hE';
  apply (AxiomExtensinality E E').2;
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

