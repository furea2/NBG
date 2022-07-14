import NBG.SetTheory.Basic

universe u


def isTopologyOf₁ (O X : Class) : Prop :=
  O ⊂ (𝒫 X)
    → (ø ∈ O ∧ X ∈ O)
    → (∀U V: Class, U ∈ O → V ∈ O → (U ∩ V) ∈ O)
    → (∀A U: Class, ((U ∈ A) → (U ∈ O)) → (⋃ A ∈ O))
def isTopologyOf₂ (C X : Class) : Prop :=
  C ⊂ (𝒫 X)
    → (ø ∈ C ∧ X ∈ C)
    → (∀D1 D2: Class, D1 ∈ C → D2 ∈ C → (D1 ∪ D2) ∈ C)
    → (∀A U: Class, ((U ∈ A) → (U ∈ C)) → (⋂ A ∈ C))

def isTopologyOf := isTopologyOf₁
class TopologicalSpace (X : Class) where
  O: Class
  isTopology: isTopologyOf O X
def isOpenSetOf (U X : Class) [topX: TopologicalSpace X] : Prop := (U ∈ topX.1)
def isClosedSetOf (D X : Class) [topX: TopologicalSpace X] : Prop := ((X ＼ D) ∈ topX.1)

