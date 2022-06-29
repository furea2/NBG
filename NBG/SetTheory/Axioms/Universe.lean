import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Extensionality

open Classical

-- 2. AxiomUniverse
axiom AxiomUniverse :
  ∃U : Class, ∀x: Class, (x∈U ↔ ∃X: Class,(x∈X))
noncomputable def U := choose AxiomUniverse

theorem UniqueU :
  isUnique (fun U => ∀x: Class, (x∈U ↔ ∃X: Class,(x∈X))) := by {
  intro U U' hU hU';
  apply (AxiomExtensionality U U').2;
  intro z;
  rw [hU, hU'];
  exact ⟨fun h => h,fun h => h⟩;
}

theorem AllSetInU {x : Class}: isSet x ↔ x∈U := by {
  apply Iff.intro;
  exact fun ⟨y, h⟩ => (choose_spec AxiomUniverse x).2 ⟨y, h⟩;
  exact fun h => (choose_spec AxiomUniverse x).1 h;
}

class Set (X : Class) where
  isSet : ∃(Y:Class), X ∈ Y
  inU   : X ∈ U
def asClass (_: Set X) := X

notation:50 X " ≠ " Y => ¬ (X ＝ Y)

theorem SetIsSet {x : Class} : Set x → isSet x := fun ⟨h, _⟩ => h

theorem SetInU (x : Class) [hx : Set x]: x ∈ U := hx.2

theorem AllSetSubsetU (X : Class) : X⊂U :=
  fun _ hx => AllSetInU.1 ⟨X, hx⟩
