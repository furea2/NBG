import NBG.SetTheory.Defs


-- 1. AxiomExtensionality
axiom AxiomExtensionality :
  ∀X Y: Class, (X＝Y ↔ ∀z, (z ∈ X ↔ z ∈ Y))

def Subset (X Y : Class) : Prop :=
  ∀z:Class, z ∈ X → z ∈ Y
instance : HasSubset Class where
  Subset := Subset
notation:50 X " ⊊ " Y => (Subset X Y) ∧ ¬ (X＝Y)
notation:50 X " ⊄ " Y => ¬ Subset X Y
notation:50 X " ⊈ " Y => ¬ Subset X Y

-- class equality
theorem ClassEqRefl (X : Class):
  X＝X := by {
  rw [AxiomExtensionality];
  intro z;
  exact ⟨fun h => h,fun h => h⟩;
}

theorem ClassEqSymm {X Y : Class}:
  X＝Y → Y＝X := by {
  rw [AxiomExtensionality, AxiomExtensionality];
  intro h;
  exact fun z => (h z).symm;
}

theorem ClassEqTrans {X Y Z : Class}:
  X＝Y → Y＝Z → X＝Z := by {
  rw [AxiomExtensionality,
      AxiomExtensionality,
      AxiomExtensionality];
  intro h1 h2 z;
  rw [h1,h2];
  exact ⟨fun h => h,fun h => h⟩;
}


-- class subset
theorem ClassSubsetRefl (X : Class):
  X⊂X := fun _ => (fun h => h)

theorem ClassSubsetSymmImplyEq {X Y : Class}:
  X⊂Y → Y⊂X → X＝Y := by {
  rw [AxiomExtensionality];
  exact fun h1 h2 z => ⟨h1 z,h2 z⟩;
}

theorem ClassSubsetTrans {X Y Z : Class}:
  X⊂Y → Y⊂Z → X⊂Z :=
fun h1 h2 z h => h2 z (h1 z h)

instance : LE Class where
  le := Subset

example {X Y : Class} : X ≤ Y → Y ≤ Z → X ≤ Z :=
ClassSubsetTrans

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


def isUnique (p : Class → Prop) :=
  ∀ (X Y : Class), p X → p Y → (X ＝ Y)


