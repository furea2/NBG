universe u

axiom Class : Type u
axiom Class.In : Class.{u} → Class.{u} → Prop
axiom Class.Eq : Class.{u} → Class.{u} → Prop
infix:50 " ∈ " => Class.In
notation:50 X " ∉ " Y => ¬ Class.In X Y
infix:50 " ＝ " => Class.Eq

def isSet (X : Class) : Prop := ∃(Y:Class), X ∈ Y
class Set (X : Class) where
  isSet : isSet X

def isProper (X : Class) : Prop := ¬ (isSet X)
class ProperClass (X : Class) where
  isProper : isProper X
