import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Pair

open Classical

-- 5. AxiomProduct
axiom AxiomProduct :
  ∀X Y: Class, ∃Z: Class,
    ∀z: Class, (z∈Z ↔ ∃x y: Class, x∈X → y∈Y → (z ＝ ＜x,y＞))
noncomputable def Product (X Y: Class) := choose (AxiomProduct X Y)
infix:50 " ✕ " => Product
noncomputable def U₂ := Product U U
noncomputable def U₃ := Product U₂ U

def isRelation (R : Class) : Prop :=
  ∀z: Class, ∃x y: Class, z∈R → x∈U → y∈U → z = ＜x,y＞
class Relation (R : Class) where
  isRelation: isRelation R

