import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Pair

open Classical

-- 5. AxiomProduct
axiom AxiomProduct :
  ∀X Y: Class, ∃Z: Class,
    ∀z: Class, (z∈Z ↔ ∃x y: Class, ∃hx: x ∈ X,∃hy: y ∈ Y,
      (z ＝ (@OrdPair_mk x y (Set.mk₁ hx) (Set.mk₁ hy))))
noncomputable def ProductClass_mk (X Y: Class) : Class :=
  choose (AxiomProduct X Y)
noncomputable def ProductClass_def (X Y: Class):
  ∀z: Class, (z ∈ (ProductClass_mk X Y) ↔ ∃x y: Class, ∃hx: x ∈ X,∃hy: y ∈ Y,
    (z ＝ (@OrdPair_mk x y (Set.mk₁ hx) (Set.mk₁ hy)))) :=
  choose_spec (AxiomProduct X Y)
noncomputable instance : HasProduct Class where
  Product := ProductClass_mk
noncomputable def U₂ := ProductClass_mk U U
noncomputable def U₃ := ProductClass_mk U₂ U

-- Todo: ProductClassIntro



-- theorem SetProductIsSet (x y : Class) [Set x] [Set y]: isSet (x ✕ y) :=
--   sorry
-- noncomputable def SetProductSet (x y : Class) [Set x] [Set y] : Set (x ✕ y) :=
--   Set.mk (SetProductIsSet x y) (AllSetInU.1 (SetProductIsSet x y))

-- Relation type
def isRelation (R : Class) : Prop :=
  ∀z: Class, z∈R ↔ ∃x y: Class, ∃_: Set x, ∃_: Set y,
    (z ＝ ＜x, y＞)
class Relation (R : Class) where
  isRelation: isRelation R

-- Function type
def isFunction (F : Class) [Relation F] : Prop :=
  ∀x x' y y': Class, ∀_: Set x, ∀_: Set x', ∀_: Set y, ∀_: Set y',
    ＜x, y＞ ∈ F → ＜x', y'＞ ∈ F → x ＝x' → y ＝ y'
class Function (F : Class) extends Relation F where
  isFunction : isFunction F
