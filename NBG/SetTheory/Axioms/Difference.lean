import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Universe

open Classical

-- 3. AxiomDifference
axiom AxiomDifference :
  ∀X Y: Class, ∃Z: Class,
    ∀u: Class, (u∈Z ↔ (u ∈ X ∧ u ∉ Y))
noncomputable def Diff (X Y: Class): Class :=
  choose (AxiomDifference X Y)
noncomputable def Diff_def (X Y: Class):
  ∀u: Class, (u ∈ (Diff X Y) ↔ (u ∈ X ∧ u ∉ Y)) :=
  choose_spec (AxiomDifference X Y)
noncomputable instance : HasDiff Class where
  Diff := Diff


-- intersection
noncomputable def IntersectionClass_mk' (X Y: Class) :=
  X ＼ (X ＼ Y)
theorem IntersectionClassExists:
  ∀X Y: Class, ∃Z: Class,
    ∀z: Class, ((z ∈ Z) ↔ (z ∈ X) ∧ (z ∈ Y)) := by {
  intro X Y;
  let inter := IntersectionClass_mk' X Y;
  exists inter;
  have inter_def:
    ∀u: Class, (u ∈ inter ↔ (u ∈ X ∧ u ∉ (X ＼ Y))) :=
    choose_spec (AxiomDifference X (X ＼ Y));
  have diff_def:
    ∀u: Class, (u ∈ (X ＼ Y) ↔ (u ∈ X ∧ u ∉ Y)) :=
    choose_spec (AxiomDifference X Y);
  sorry;
}
noncomputable def IntersectionClass_mk (X Y: Class) :=
  choose (IntersectionClassExists X Y)
noncomputable instance : HasInter Class where
  Inter := IntersectionClass_mk
noncomputable def IntersectionClass_def (X Y: Class):
  ∀z: Class, ((z ∈ (X ∩ Y)) ↔ (z ∈ X) ∧ (z ∈ Y)) :=
  choose_spec (IntersectionClassExists X Y)
theorem IntersectionClassIntro (X Y: Class) :
  ∀z: Class, (z ∈ (X ∩ Y)) ↔ (z ∈ X) ∧ (z ∈ Y) :=
  IntersectionClass_def X Y
def isIntersectionClass {X Y: Class} (I: Class) :=
  ∀z: Class, (z ∈ I) ↔ (z ∈ X) ∧ (z ∈ Y)
class IntersectionClass {X Y: Class} (I : Class) where
  isIntersectionClass: (@isIntersectionClass X Y I)

-- union
noncomputable def UnionClass_mk' (X Y: Class) :=
  U ＼ ((U ＼ X) ∩ (U ＼ Y))
theorem UnionClassExists:
  ∀X Y: Class, ∃Z: Class,
    ∀z: Class, ((z ∈ Z) ↔ (z ∈ X) ∨ (z ∈ Y)) := by {
  intro X Y;
  let union := UnionClass_mk' X Y;
  exists union;
  have union_def:
    ∀u: Class, (u ∈ union ↔ (u ∈ U ∧ u ∉ ((U ＼ X) ∩ (U ＼ Y)))) :=
    choose_spec (AxiomDifference U ((U ＼ X) ∩ (U ＼ Y)));
  have inter_def:
    ∀u: Class, (u ∈ ((U ＼ X) ∩ (U ＼ Y)) ↔ (u ∈ (U ＼ X) ∧ u ∈ (U ＼ Y))) :=
    choose_spec (IntersectionClassExists (U ＼ X) (U ＼ Y));
  have diff_x_def:
    ∀u: Class, (u ∈ (U ＼ X) ↔ (u ∈ U ∧ u ∉ X)) :=
    choose_spec (AxiomDifference U X);
  have diff_y_def:
    ∀u: Class, (u ∈ (U ＼ Y) ↔ (u ∈ U ∧ u ∉ Y)) :=
    choose_spec (AxiomDifference U Y);
  sorry;
}
noncomputable def UnionClass_mk (X Y: Class) :=
  choose (UnionClassExists X Y)
noncomputable instance : HasUnion Class where
  Union := UnionClass_mk
noncomputable def UnionClass_def (X Y: Class):
  ∀z: Class, ((z ∈ (X ∪ Y)) ↔ (z ∈ X) ∨ (z ∈ Y)) :=
  choose_spec (UnionClassExists X Y)
theorem UnionClassIntro (X Y: Class) :
  ∀z: Class, (z ∈ (X ∪ Y)) ↔ (z ∈ X) ∨ (z ∈ Y) :=
  UnionClass_def X Y
def isUnionClass {X Y: Class} (I: Class) :=
  ∀z: Class, (z ∈ I) ↔ (z ∈ X) ∨ (z ∈ Y)
class UnionClass {X Y: Class} (I : Class) where
  isUnionClass: (@isUnionClass X Y I)


-- empty class
noncomputable def EmptyClass_mk' : Class :=
  U ＼ U
theorem EmptyClassExists:
  ∃Z: Class, ∀u: Class, (¬ u ∈ Z) := by {
  let emp := EmptyClass_mk';
  exists emp;
  have emp_def: ∀u: Class, (u ∈ emp ↔ (u ∈ U ∧ u ∉ U)) :=
    choose_spec (AxiomDifference U U);
  exact fun z h => ((emp_def z).1 h).2 ((emp_def z).1 h).1
}
noncomputable def EmptyClass_mk : Class :=
  choose EmptyClassExists
notation " ø " => EmptyClass_mk
def EmptyClass_def:
  ∀(z : Class), ¬ z ∈ ø :=
  choose_spec EmptyClassExists

def isEmptyClass (E : Class) : Prop := ∀(z : Class), ¬ z ∈ E
class EmptyClass (E : Class) where
  isEmptyClass: isEmptyClass E

def isNonEmptyClass (X : Class) : Prop := ∃(z : Class), z ∈ X
class NonEmptyClass (X : Class) where
  isNonEmptyClass: isNonEmptyClass X

theorem EmptyClassIsNotNonEmpty {X : Class}:
  isEmptyClass X → ¬ isNonEmptyClass X :=
  fun h1 ⟨z, h2⟩ => (h1 z) h2
theorem NonEmptyClassIsNotEmpty {X : Class}:
  isNonEmptyClass X → ¬ isEmptyClass X :=
  fun ⟨z, h1⟩ h2 => (h2 z) h1

-- -- symmdiff
-- noncomputable def SymmDiffClass_mk' (X Y: Class) :=
--   (X ＼ Y) ∩ (Y ＼ X)
-- theorem SymmDiffClassExists (X Y: Class):
--   ∃Z:Class,
--     ∀z: Class, (z ∈ Z) ↔
--     (z ∈ (X ＼ Y)) ∧ (z ∈ (Y ＼ X)) := by {
--   sorry;
-- }
-- noncomputable def SymmDiffClass_mk (X Y: Class) :=
--   choose (SymmDiffClassExists X Y)
-- noncomputable def SymmDiffClass_def (X Y: Class) :=
--   choose_spec (SymmDiffClassExists X Y)
-- infix:50 " △ " => SymmDiffClass_mk
-- theorem SymmDiffClassIntro (X Y: Class) :
--   ∀z: Class, (z ∈ (X △ Y)) ↔
--     (z ∈ (X ＼ Y)) ∧ (z ∈ (Y ＼ X)) :=
--   SymmDiffClass_def X Y
-- def isSymmDiffClass {X Y: Class} (Z: Class) :=
--   ∀z: Class, (z ∈ Z) ↔ (z ∈ (X ＼ Y) ∧ z ∈ (Y ＼ X))
-- class SymmDiffClass {X Y: Class} (I : Class) where
--   isSymmDiffClass: (@isSymmDiffClass X Y I)


-- empty class property
theorem EmptyHasNoClass : ∀(X : Class), ¬(X ∈ ø) :=
  EmptyClass_def

theorem EmptySetIsUnique :
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

