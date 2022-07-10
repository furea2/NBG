import NBG.SetTheory.Ordinal.Transitive
import NBG.SetTheory.Relation.Order

open Classical


theorem EUpIsRelation (x: Class) :
  isRelation (Restriction E x) := sorry
theorem EUpIsAsymmetric (x: Class) :
  @isAntisymmetric (Restriction E x) ⟨EUpIsRelation x⟩ := sorry
theorem EUpIsTransitive (x: Class) :
  isTransitive (Restriction E x) := sorry
theorem EUpIsOrder (x: Class) : @isOrder (Restriction E x) ⟨EUpIsRelation x⟩ := sorry

theorem OrderEUp (x: Class) : Order (Restriction E x) := sorry

def IsIrreflexiveWellOrderOn (Restriction E x: Class) : Prop := sorry

def isOrdinal (x: Class) [Set x] :=
  isTransitive x
    ∧ (@isIrreflexive (Restriction E x) ⟨EUpIsRelation x⟩)
      ∧ (@isWellOrder (Restriction E x) (OrderEUp x))
class Ordinal (x: Class) [Set x] where
  isOrdinal: isOrdinal x

theorem OrdinalClassExists:
  ∃On: Class, ∀x: Class, ∀_:Set x,
    x ∈ On ↔ isOrdinal x := sorry

noncomputable def On : Class :=
  choose OrdinalClassExists
noncomputable def On_def:
  ∀x: Class, ∀_:Set x,
    x ∈ On ↔ isOrdinal x :=
  choose_spec OrdinalClassExists

theorem On_property_1:
  isTransitive On := sorry
-- theorem On_property_2:
--   IsIrreflexiveWellOrderOn (Restriction E On) On := sorry
theorem On_property_3:
  isTransitive On := sorry
theorem On_property_4:
  ∀x:Class, ((hx: x∈On) → (x ∪ (@Singleton_mk x (Set.mk₁ hx))) ∈ On) := sorry
theorem On_property_5:
  ∀x:Class, ∀_:Set x, (x⊂On → ⋃ x ∈ On) := sorry
theorem On_property_6:
  isProper On := sorry
theorem OmegaIsInOn: ω ⊂ On := sorry
theorem OmegaSubsetOn: ω ∈ On := sorry

