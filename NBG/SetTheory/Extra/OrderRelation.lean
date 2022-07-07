import NBG.SetTheory.Ordinal.Transitive
import NBG.SetTheory.Extra.Identity
import NBG.SetTheory.Extra.WellFounded


def isAntisymmetric (R : Class) [Relation R] : Prop :=
  (R ∩ RelInv R) ⊂ IdClass
class Antisymmetric (R : Class) extends Relation R where
  isAntisymmetric : isAntisymmetric R

def isOrder (R : Class) [Relation R] : Prop :=
  isTransitive R ∧ isAntisymmetric R
class Order (R : Class) extends Relation R where
  isOrder : isOrder R

def isLinearOrder (R : Class) [Order R] : Prop :=
  (Dom (R ∪ RelInv R) ✕ Dom (R ∪ RelInv R)) ⊂ ((R ∪ IdClass) ∪ (RelInv R))
class LinearOrder (R : Class) extends Order R where
  isLinearOrder: isLinearOrder R

def isWellOrder (R : Class) [Order R] : Prop :=
  isWellFounded R ∧ isLinearOrder R
class WellOrder (R : Class) extends Order R where
  isWellOrder: isWellOrder R
