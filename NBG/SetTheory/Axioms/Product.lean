import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Pair

open Classical

-- 5. AxiomProduct
axiom AxiomProduct :
  ∀X Y: Class, ∃Z: Class,
    ∀z: Class, (z∈Z ↔ ∃x y: Class, (hx: x∈X) → (hy: y∈Y)
      → (z ＝ OrdPair' x y (AllSetInU.1 ⟨X, hx⟩) (AllSetInU.1 ⟨Y, hy⟩)))
noncomputable def Product (X Y: Class) := choose (AxiomProduct X Y)
noncomputable instance : HasProduct Class where
  Product := Product
noncomputable def U₂ := Product U U
noncomputable def U₃ := Product U₂ U

theorem ProductIsSet (X Y : Class):
  isSet (X ✕ Y) := sorry

def isRelation (R : Class) : Prop :=
  ∀z: Class, z∈R → ∃x y: Class, (hx: x∈U) → (hy: y∈U) → (z = OrdPair' x y hx hy)
class Relation (R : Class) where
  isRelation: isRelation R

