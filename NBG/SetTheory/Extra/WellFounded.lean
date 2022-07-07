-- import NBG.SetTheory.Axioms.Basic
import NBG.SetTheory.Axioms.Basic


def isSetLike (R : Class) [Relation R] : Prop :=
  ∀x: Class,∀_:Set x,
    isSet ((@Im (RelInv R) {x} ⟨RelInvRelationIsRelation⟩) ＼ {x})
class SetLike (R : Class) extends Relation R where
  isSetLike: isSetLike R

def isWellFounded (R : Class) [Relation R] : Prop :=
  ∀X:Class,∀_:NonEmptyClass X,
    ∃x:Class,∃hx:x∈X, ((((@Im (RelInv R) (@Singleton_mk x (Set.mk₁ hx)) ⟨RelInvRelationIsRelation⟩) ＼ (@Singleton_mk x (Set.mk₁ hx)))) ∩ X) ＝ ø
class WellFoundeRelation (R : Class) extends Relation R where
  isWellFounded: isWellFounded R
