import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Extensionality

open Classical

-- 2. AxiomUniverse
axiom AxiomUniverse :
  ∃U : Class, ∀x: Class, (x∈U ↔ ∃X: Class,(x∈X))
noncomputable def U: Class :=
  choose AxiomUniverse
noncomputable def U_def:
  ∀x: Class, (x∈U ↔ ∃X: Class,(x∈X)) :=
  choose_spec AxiomUniverse

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
  {exact fun ⟨y, h⟩ => (choose_spec AxiomUniverse x).2 ⟨y, h⟩;}
  {exact fun h => (choose_spec AxiomUniverse x).1 h;}
}

-- type Set
class Set (X : Class) where
  isSet : isSet X
  inU   : X ∈ U
def Set.mk₁ {X Y: Class} (h: X ∈ Y): Set X :=
  Set.mk ⟨Y, h⟩ (AllSetInU.1 ⟨Y, h⟩)
def Set.mk₂ {X: Class} (hx: X ∈ U): Set X :=
  Set.mk (AllSetInU.2 hx) hx

-- type SetType
class SetType where
  X : Class
  x : Set X
def SetType.mk₁ {X Y: Class} (h: X ∈ Y): SetType :=
  SetType.mk X (Set.mk₁ h)
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
