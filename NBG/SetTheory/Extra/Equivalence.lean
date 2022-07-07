import NBG.SetTheory.Extra.Identity


def isSymmetric (R : Class) [Relation R] : Prop := (R ＝ RelInv R)
class Symmetric (R : Class) extends Relation R where
  isSymmetric : isSymmetric R

def isTransitive (R : Class) [Relation R] : Prop :=
  ∀x y z: Class, ∀_: Set x, ∀_: Set y, ∀_: Set z,
    (＜x, y＞ ∈ R ∧ ＜y, z＞ ∈ R) → ＜x, z＞ ∈ R
class Transitive (R : Class) extends Relation R where
  isTransitive : isTransitive R

def isEquivalence (R : Class) [Relation R] : Prop :=
  isSymmetric R ∧ isTransitive R
class EqivalenceRelation (R : Class) extends Symmetric R, Transitive R

theorem IdentityFunctionIsEquivalenceRelation:
  @isEquivalence IdClass ⟨IdClassIsRelation⟩ := sorry

