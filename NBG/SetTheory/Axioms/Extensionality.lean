import NBG.SetTheory.Defs


-- 1. AxiomExtensionality
axiom AxiomExtensionality :
  ∀X Y: Class, (X＝Y ↔ ∀z, (z ∈ X ↔ z ∈ Y))

def ClassSubset (X Y : Class) : Prop :=
  ∀z:Class, z ∈ X → z ∈ Y
instance : HasSubset Class where
  Subset := ClassSubset
notation:50 X " ⊊ " Y => (ClassSubset X Y) ∧ ¬ (X＝Y)
notation:50 X " ⊄ " Y => ¬ ClassSubset X Y
notation:50 X " ⊈ " Y => ¬ ClassSubset X Y

-- class equality
theorem ClassEq.refl (X : Class):
  X＝X := by {
  rw [AxiomExtensionality];
  intro z;
  exact ⟨fun h => h,fun h => h⟩;
}

theorem ClassEq.symm {X Y : Class}:
  X＝Y → Y＝X := by {
  rw [AxiomExtensionality, AxiomExtensionality];
  intro h;
  exact fun z => (h z).symm;
}

theorem ClassEq.trans {X Y Z : Class}:
  X＝Y → Y＝Z → X＝Z := by {
  rw [AxiomExtensionality,
      AxiomExtensionality,
      AxiomExtensionality];
  intro h1 h2 z;
  rw [h1,h2];
  exact ⟨fun h => h,fun h => h⟩;
}

-- -- class in
-- private theorem EqClassEqIn' {X Y Z: Class}:
--   X ＝ Y → (X ∈ Z → Y ∈ Z) := by {
--   intro h hx;
--   by_cases hy: Y ∈ Z;
--   {exact hy;}
--   {
--     apply False.elim;
--     sorry;
--   }
-- }

-- theorem EqClassEqIn (X Y Z: Class):
--   X ＝ Y → (X ∈ Z ↔ Y ∈ Z) := by {
--   intro h;
--   apply Iff.intro;
--   {exact EqClassEqIn' h;}
--   {exact EqClassEqIn' (ClassEq.symm h);}
-- }


-- class subset
theorem ClassSubset.refl (X : Class):
  X⊂X := fun _ => (fun h => h)

theorem ClassSubsetSymmImplyEq {X Y : Class}:
  X⊂Y → Y⊂X → X＝Y := by {
  rw [AxiomExtensionality];
  exact fun h1 h2 z => ⟨h1 z,h2 z⟩;
}

theorem ClassSubset.trans {X Y Z : Class}:
  X⊂Y → Y⊂Z → X⊂Z :=
fun h1 h2 z h => h2 z (h1 z h)

instance : LE Class where
  le := ClassSubset

example {X Y : Class} : X ≤ Y → Y ≤ Z → X ≤ Z :=
ClassSubset.trans

theorem EqIffSubsetMutually (X Y : Class):
  X＝Y ↔ (X ⊂ Y ∧ Y ⊂ X) := by {
    rw [AxiomExtensionality];
    apply Iff.intro;
    case mp => {
      intro h;
      exact ⟨fun z => (h z).1,fun z => (h z).2⟩
    }
    case mpr => {
      exact fun h z => ⟨h.1 z,h.2 z⟩
    }
}

theorem ClassEqMenberImpMenber {x y z: Class}:
  (x ＝ y ∧ y ∈ z) → x ∈ z :=
  fun h => @RewiteClass (fun x => x ∈ z) y x ⟨ClassEq.symm h.1,h.2⟩


def isUnique (p : Class → Prop) :=
  ∀ (X Y : Class), p X → p Y → (X ＝ Y)


