import NBG.SetTheory.Defs


-- 1. AxiomExtensinality
axiom AxiomExtensinality :
  ∀X Y: Class, (X＝Y ↔ ∀z, (z ∈ X ↔ z ∈ Y))

def Subset (X Y : Class) : Prop :=
  ∀z:Class, z ∈ X → z ∈ Y
infix:50 " ⊂ " => Subset
infix:50 " ⊆ " => Subset
-- notation:50 X " ⊂ " Y => (Subset X Y) ∧ ¬ (X＝Y)
notation:50 X " ⊄ " Y => ¬ Subset X Y
notation:50 X " ⊈ " Y => ¬ Subset X Y

theorem ClassEqRefl (X : Class):
  X＝X := by {
  rw [AxiomExtensinality];
  intro z;
  exact ⟨fun h => h,fun h => h⟩;
}

theorem EqIffSubsetMutually (X Y : Class):
  X＝Y ↔ (X ⊂ Y ∧ Y ⊂ X) := by {
    rw [AxiomExtensinality];
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