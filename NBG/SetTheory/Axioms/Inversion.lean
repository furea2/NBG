import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Product

open Classical

-- 6. AxiomInversion
axiom AxiomInversion :
  ∀X: Class, ∃Y: Class,
    ∀x y: SetType, ((＜x, y＞c)∈X ↔ (＜y, x＞c)∈Y)
noncomputable def RelInv (R: Class) := choose (AxiomInversion R)
noncomputable def RelInv_def (R: Class) := choose_spec (AxiomInversion R)

theorem RelIffRelInRelInv (R: Class) :
  (isRelation R) ↔ (R ＝ RelInv (RelInv R)) := by {
  apply Iff.intro;
  case mp => {
    unfold isRelation;
    intro h;
    apply (AxiomExtensionality R (RelInv (RelInv R))).2;
    intro z;
    have h := h z;
    apply Iff.intro;
    case mp => {
      intro hz;
      have := h hz;
      sorry;
    }
    case mpr => {
      sorry;
    }
  };
  case mpr => {sorry};
}

