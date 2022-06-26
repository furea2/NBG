import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Domain

open Classical

-- 8. AxiomMembership
axiom AxiomMembership :
  ∃E: Class, ∀x y: Class,
    x∈U → y∈U → (＜x,y＞∈E ↔ x∈y)
noncomputable def E := choose AxiomMembership
-- theorem DomEEqUniv : (Dom E) ＝ U := sorry
def isFunction (F : Class) [Relation F] : Prop :=
  ∀x x' y y': Class, ＜x,y＞∈F → ＜x',y'＞∈F → x＝x' ∧ y＝y'
class Function (F : Class) extends Relation F where
  isFunction : isFunction F
def Apply (F X: Class) : Class := sorry

noncomputable def UnionAll (X : Class) :=
  Dom (E ∩ (U ✕ X))
noncomputable def InterAll (X : Class) :=
  Diff U (Dom ((Diff U₂ E) ∩ (U ✕ X)))
noncomputable def PowerSet (X : Class) :=
  Diff U (Dom ((RelInv E) ∩ (U ✕ (Diff U X))))
notation "⋃" X => UnionAll X
notation "⋂" X => InterAll X
notation "𝒫" X => PowerSet X

theorem UnivIsClosedPowerSet:
  U ＝ 𝒫 U := sorry

