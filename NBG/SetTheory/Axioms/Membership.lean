import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Domain

open Classical

-- 8. AxiomMembership
axiom AxiomMembership :
  ∃E: Class, ∀x y: SetType, (＜x, y＞c ∈ E ↔ x∈y)
noncomputable def E := choose AxiomMembership
noncomputable def E_def := choose_spec AxiomMembership
-- theorem DomEEqUniv : (Dom E) ＝ U := sorry
def isFunction (F : Class) [Relation F] : Prop :=
  ∀x x' y y': SetType,
    ＜x, y＞c ∈ F → ＜x', y'＞c ∈ F → x.1＝x'.1 ∧ y.1＝y'.1
class Function (F : Class) extends Relation F where
  isFunction : isFunction F
def Apply (F x: Class) {h: x∈ (Dom F)} [hF: Function F] : Class := by {
  have F_def := hF.1.1;
  unfold isRelation at F_def;
  sorry;
}

noncomputable def UnionAll (X : Class) :=
  Dom (E ∩ (U ✕ X))
noncomputable instance : HasUnionAll Class where
  UnionAll := UnionAll

noncomputable def InterAll (X : Class) :=
  Diff U (Dom ((Diff U₂ E) ∩ (U ✕ X)))
noncomputable instance : HasInterAll Class where
  InterAll := InterAll

noncomputable def PowerSet (X : Class) :=
  Diff U (Dom ((RelInv E) ∩ (U ✕ (Diff U X))))
noncomputable instance : HasPow Class where
  Pow := PowerSet

theorem UnivIsClosedPowerSet:
  U ＝ 𝒫 U := sorry

