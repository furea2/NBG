import NBG.SetTheory.Ordinal.Transitive
open Classical


noncomputable def E_Up (x: Class) := E ∩ (x ✕ x)

def IsIrreflexiveWellOrderOn (E_Up x: Class) : Prop := sorry

def isOrdinal (x: Class) [Set x] :=
  isTransitive x ∧ (IsIrreflexiveWellOrderOn (E_Up x) x)
class Ordinal (x: Class) [Set x] where
  isOrdinal: isOrdinal x

theorem OrdinalClassExists:
  ∃On: Class, ∀x: Class, ∀_:Set x,
    x ∈ On ↔ isOrdinal x := sorry

noncomputable def On : Class := (choose OrdinalClassExists)
noncomputable def On_def := (choose_spec OrdinalClassExists)

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
theorem On_property_7:
  ω ⊂ On := sorry
theorem On_property_8:
  ω ∈ On := sorry

