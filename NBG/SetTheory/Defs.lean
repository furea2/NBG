import NBG.Init.Notations

universe u

axiom Class : Type u
axiom Class.In : Class → Class → Prop
axiom Class.Eq : Class → Class → Prop

instance : HasEq Class where
  Eq := Class.Eq
notation:50 X " ≠ " Y => ¬ (X ＝ Y)

instance : HasMem Class where
  Mem := Class.In
notation:50 X " ∉ " Y => ¬ X ∈ Y

def isSet (X : Class) : Prop := ∃(Y:Class), X ∈ Y
class Set (X : Class) where
  isSet : ∃(Y:Class), X ∈ Y

theorem SetIsSet {x : Class} : Set x → isSet x := fun ⟨Y, h⟩ => ⟨Y, h⟩

def isProper (X : Class) : Prop := ¬ (isSet X)
class ProperClass (X : Class) where
  isProper : isProper X
