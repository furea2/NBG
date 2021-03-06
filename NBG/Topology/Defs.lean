import NBG.SetTheory.Basic

universe u


def isTopologyOfâ (O X : Class) : Prop :=
  O â (ð« X)
    â (Ã¸ â O â§ X â O)
    â (âU V: Class, U â O â V â O â (U â© V) â O)
    â (âA U: Class, ((U â A) â (U â O)) â (â A â O))
def isTopologyOfâ (C X : Class) : Prop :=
  C â (ð« X)
    â (Ã¸ â C â§ X â C)
    â (âD1 D2: Class, D1 â C â D2 â C â (D1 âª D2) â C)
    â (âA U: Class, ((U â A) â (U â C)) â (â A â C))

def isTopologyOf := isTopologyOfâ
class TopologicalSpace (X : Class) where
  O: Class
  isTopology: isTopologyOf O X
def isOpenSetOf (U X : Class) [topX: TopologicalSpace X] : Prop := (U â topX.1)
def isClosedSetOf (D X : Class) [topX: TopologicalSpace X] : Prop := ((X ï¼¼ D) â topX.1)

