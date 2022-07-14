import NBG.SetTheory.Basic

def isOpelationOf (m X : Class) :=
  {_:Relation m} → isFunction m
    → (Dom m ＝ (X ✕ X))
    → (Rng m ＝ X)
class Magma (X : Class.{u}) where
  oper_rel: Class.{u}
  isOpelation: isOpelationOf oper X
  oper (a b: Class.{u}): Class.{u}

