import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Pair

open Classical

-- 5. AxiomProduct
axiom AxiomProduct :
  ∀X Y: Class, ∃Z: Class,
    ∀z: Class, (z∈Z ↔ ∃x y: Class, ∃hx: x ∈ X,∃hy: y ∈ Y,
      (z ＝ (@OrdPair_mk x y (Set.mk₁ hx) (Set.mk₁ hy))))
noncomputable def Product (X Y: Class) := choose (AxiomProduct X Y)
noncomputable def Product_def (X Y: Class) := choose_spec (AxiomProduct X Y)
noncomputable instance : HasProduct Class where
  Product := Product
noncomputable def U₂ := Product U U
noncomputable def U₃ := Product U₂ U

theorem SetProductIsSet (x y : Class) [Set x] [Set y]: isSet (x ✕ y) :=
  sorry
-- noncomputable def ProductSet (x y : Class) [Set x] [Set y] :=
--   Set.mk₁ (SetProductIsSet x y).2

def isRelation (R : Class) : Prop :=
  ∀z: Class, z∈R → ∃x y: Class, ∃_: Set x, ∃_: Set y,
    (z ＝ ＜x, y＞)
class Relation (R : Class) where
  isRelation: isRelation R

