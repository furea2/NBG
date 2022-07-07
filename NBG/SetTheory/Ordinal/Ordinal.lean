import NBG.SetTheory.Extra.Reflexive
import NBG.SetTheory.Ordinal.Transitive
import NBG.SetTheory.Extra.OrderRelation
open Classical


noncomputable def E_Up (x: Class) := E ∩ (x ✕ x)

theorem EUpIsRelation (x: Class) :
  isRelation (E_Up x) := sorry
-- theorem EUpIsOrder (x: Class) [Relation R]:
--   @isOrder (E_Up x) ⟨EUpIsRelation x⟩ := sorry
axiom EUpIsOrder {x: Class}: Order (E_Up x)

def IsIrreflexiveWellOrderOn (E_Up x: Class) : Prop := sorry

def isOrdinal (x: Class) [Set x] :=
  isTransitive x
    ∧ (@isIrreflexive (E_Up x) ⟨EUpIsRelation x⟩)
      ∧ (@isWellOrder (E_Up x) EUpIsOrder)
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
theorem On_property_2:
  IsIrreflexiveWellOrderOn (E_Up On) On := sorry
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

