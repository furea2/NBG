import NBG.Init.Base

universe u

axiom Class : Type u
axiom Class.In : Class → Class → Prop
axiom Class.Eq : Class → Class → Prop

instance : HasEq Class where
  Eq := Class.Eq
notation:50 X " ≠ " Y => ¬ (X ＝ Y)

instance : HasIn Class where
  In := Class.In
notation:50 X " ∉ " Y => ¬ X ∈ Y

def isSet (X : Class) : Prop := ∃(Y:Class), X ∈ Y

def isProper (X : Class) : Prop := ¬ (isSet X)
class ProperClass (X : Class) where
  isProper : isProper X
