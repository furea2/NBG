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

-- set type
class Set (X : Class) where
  isSet : ∃(Y:Class), X ∈ Y
  inU   : X ∈ U
def Set.mk₁ (X: Class) (hx: isSet X) :=
  Set.mk hx (AllSetInU.1 hx)
def Set.mk₂ {X: Class} (hx: X ∈ U): Set X :=
  Set.mk (AllSetInU.2 hx) hx


class SetType where
  X : Class
  x : Set X
def SetType.mk₁ (X: Class) (hx: isSet X): SetType :=
  SetType.mk X ⟨hx,AllSetInU.1 hx ⟩
def SetType.mk₂ (X: Class) (x: X ∈ U): SetType :=
  SetType.mk X ⟨AllSetInU.2 x, x⟩

def SetType.Eq (X Y: SetType) : Prop := Class.Eq X.1 Y.1
def SetType.In (X Y: SetType) : Prop := Class.In X.1 Y.1

instance : HasEq SetType where
  Eq := SetType.Eq
instance : HasIn SetType where
  In := SetType.In

def SetType.asClass (x: SetType) := x.1
def SetType.asClass_def {X: Class} {hX: Set X}: (SetType.mk X hX).1 = X := by rfl;
def SetType.asClass_def₁ {X: Class} {hX: isSet X}: (SetType.mk₁ X hX).1 = X := by rfl;
def SetType.asClass_def₂ {X: Class} {hX: X∈U}: (SetType.mk₂ X hX).1 = X := by rfl;

theorem SetIsSet {x : Class} : Set x → isSet x := fun ⟨h, _⟩ => h
theorem SetInU (x : Class) [hx : Set x]: x ∈ U := hx.2
theorem AllSetSubsetU (X : Class) : X⊂U :=
  fun _ hx => AllSetInU.1 ⟨X, hx⟩
