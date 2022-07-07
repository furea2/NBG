import NBG.SetTheory.Extra.Identity


def isReflexive (R : Class) [Relation R] : Prop :=
  Restriction IdClass (Dom (R ∪ RelInv R)) ⊂ R
class Reflexive (R : Class) extends Relation R where
  isReflexive : isReflexive R

def isIrreflexive (R : Class) [Relation R] : Prop :=
  (R ∩ IdClass) ＝ ø
class Irreflexive (R : Class) extends Relation R where
  isIrreflexive : isIrreflexive R


