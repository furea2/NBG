import NBG.SetTheory.Axioms.Extensionality

-- Classoid
private theorem ClassEqIsEquivalence : @Equivalence Class Class.Eq :=
  { refl := ClassEqRefl, symm := ClassEqSymm, trans := ClassEqTrans }

instance Classoid : Setoid Class where
  r     := Class.Eq
  iseqv := ClassEqIsEquivalence

def Class' : Type u := Quotient Classoid

theorem Classoid.sound {X Y : Class}:
  X ＝ Y → (Quot.mk Class.Eq X) = (Quot.mk Class.Eq Y) :=
fun h => Quot.sound h

theorem Classoid.refl : ∀(X : Class'), X=X := by {
  intro _;
  apply Quot.inductionOn (motive := fun X => X=X);
  intro X;
  apply Classoid.sound;
  exact ClassEqRefl X;
}