import NBG.SetTheory.Relation.Reflexive


def isSymmetric (R : Class) [Relation R] : Prop := (R ＝ RelInv R)
class Symmetric (R : Class) extends Relation R where
  isSymmetric : isSymmetric R

def isTransitiveRelation (R : Class) [Relation R] : Prop :=
  ∀x y z: Class, ∀_: Set x, ∀_: Set y, ∀_: Set z,
    (＜x, y＞ ∈ R ∧ ＜y, z＞ ∈ R) → ＜x, z＞ ∈ R
class TransitiveRelation (R : Class) extends Relation R where
  isTransitiveRelation : isTransitiveRelation R

def isEquivalence (R : Class) [Relation R] : Prop :=
  isSymmetric R ∧ isTransitiveRelation R
class EqivalenceRelation (R : Class) extends Symmetric R, TransitiveRelation R

theorem IdentityFunctionIsEquivalenceRelation:
  @isEquivalence IdClass ⟨IdClassIsRelation⟩ := sorry

theorem EquivalenceRelationImpDomEqRng (R : Class) [EqivalenceRelation R]:
  Dom R ＝ Rng R := sorry

theorem EquivalenceRelationIsReflexive (R : Class) [EqivalenceRelation R]:
  isReflexive R := sorry

-- Equivalence Class

