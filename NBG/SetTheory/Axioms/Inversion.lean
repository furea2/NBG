import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Product

open Classical

-- 6. AxiomInversion
axiom AxiomInversion :
  ∀X: Class, ∃Y: Class,
    ∀x y: Class, x∈U → y∈U → (＜x,y＞∈X ↔ ＜y,x＞∈Y)
noncomputable def RelInv (R: Class) := choose (AxiomInversion R)

theorem RelIffRelInRelInv (R: Class) :
  (isRelation R) ↔ (R ＝ RelInv (RelInv R)) := by {
  apply Iff.intro;
  case mp => {
    unfold isRelation;
    intro h;
    apply (AxiomExtensionality R (RelInv (RelInv R))).2;
    intro z;
    have ⟨x,y,h⟩ := h z;
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

