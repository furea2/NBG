import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Domain

open Classical

-- 8. AxiomMembership
axiom AxiomMembership :
  ∃E: Class, ∀x y: Class,
    (hx: x∈U) → (hy: y∈U) → ((OrdPair' x y hx hy)∈E ↔ x∈y)
noncomputable def E := choose AxiomMembership
-- theorem DomEEqUniv : (Dom E) ＝ U := sorry
def isFunction (F : Class) [Relation F] : Prop :=
  ∀x x' y y': Class,
    (hx: x∈U) → (hx': x'∈U) → (hy: y∈U) → (hy': y'∈U)
      → (OrdPair' x y hx hy)∈F → (OrdPair' x' y' hx' hy')∈F → x＝x' ∧ y＝y'
class Function (F : Class) extends Relation F where
  isFunction : isFunction F
def Apply (F X: Class) : Class := sorry

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

