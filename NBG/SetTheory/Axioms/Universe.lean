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

-- type Set
class Set (X : Class) where
  isSet : isSet X
  inU   : X ∈ U
def Set.mk₁ {X: Class} (hx: isSet X): Set X :=
  Set.mk hx (AllSetInU.1 hx)
def Set.mk₂ {X: Class} (hx: X ∈ U): Set X :=
  Set.mk (AllSetInU.2 hx) hx

-- type SetType
class SetType where
  X : Class
  x : Set X
def SetType.mk₁ (X: Class) (hx: isSet X): SetType :=
  SetType.mk X (Set.mk₁ hx) 
def SetType.mk₂ (X: Class) (hx: X ∈ U): SetType :=
  SetType.mk X (Set.mk₂ hx) 

def SetType.Eq (X Y: SetType) : Prop := X.1 ＝ Y.1
def SetType.In (X Y: SetType) : Prop := X.1 ∈ Y.1
instance : HasEq SetType where
  Eq := SetType.Eq
instance : HasIn SetType where
  In := SetType.In

theorem AllSetSubsetU (X : Class) : X⊂U :=
  fun _ hx => AllSetInU.1 ⟨X, hx⟩
