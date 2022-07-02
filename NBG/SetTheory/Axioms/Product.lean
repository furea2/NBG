import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Pair

open Classical

-- 5. AxiomProduct
axiom AxiomProduct :
  ∀X Y: Class, ∃Z: Class,
    ∀z: Class, (z∈Z ↔ ∃x y: SetType, (hx: x.1 ∈X) → (hy: y.1 ∈Y)
      → (z ＝ ＜x, y＞c))
noncomputable def Product (X Y: Class) := choose (AxiomProduct X Y)
noncomputable def Product_def (X Y: Class) := choose_spec (AxiomProduct X Y)
noncomputable instance : HasProduct Class where
  Product := Product
noncomputable def U₂ := Product U U
noncomputable def U₃ := Product U₂ U

theorem SetProductIsSet (X Y : SetType):
  isSet (X.1 ✕ Y.1) := sorry
noncomputable def ProductSet (X Y: SetType) :=
  SetType.mk₁ (X.1 ✕ Y.1) (SetProductIsSet X Y)

def isRelation (R : Class) : Prop :=
  ∀z: Class, z∈R → ∃x y: SetType, (z ＝ ＜x, y＞c)
class Relation (R : Class) where
  isRelation: isRelation R

