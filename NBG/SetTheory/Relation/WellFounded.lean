import NBG.SetTheory.Axioms.Basic
import NBG.SetTheory.Relation.Equivalence

open Classical

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


theorem InitIntervalExisits (R x : Class) [Relation R] [Set x]:
  ∃init_interval: Class, ∀z: Class,
    (z ∈ init_interval ↔ ∃_:Set z, ＜z,x＞ ∈ R) := sorry

noncomputable def InitInterval (R x : Class) [Relation R] [Set x]: Class :=
  choose (InitIntervalExisits R x)
noncomputable def InitInterval_def (R x : Class) [Relation R] [Set x]:
  ∀z:Class,
    (z ∈ (InitInterval R x) ↔ ∃_:Set z, ＜z,x＞ ∈ R) :=
  choose_spec (InitIntervalExisits R x)

theorem InitIntervalIsEmptyIf (R x : Class) [Relation R] [Set x]:
  (x ∉ Rng R) → isEmptyClass (InitInterval R x) := sorry

theorem InitEIntervalRelation' (x : Class) [Set x]:
  (@InitInterval E x ⟨EIsRelation⟩ _) ＝ (x＼{x}) := sorry

theorem InitEIntervalRelation (x : Class) [Set x]:
  (@InitInterval E x ⟨EIsRelation⟩ _) ＝ x := sorry

theorem InitEIntervalIsSetLike (x : Class) [Set x]:
  @isSetLike E ⟨EIsRelation⟩ := sorry

theorem WellFoundedIff (R x : Class) [TransitiveRelation R] [SetLike R] [Set x]:
  isWellFounded R ↔ (∀a,∀_:Set a,∀_:a⊂(Rng R),
    ∃y,∃hy:y∈a, ((@InitInterval R y _ (Set.mk₁ hy)) ∩ y) ＝ ø ) := sorry

