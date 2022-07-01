import NBG.SetTheory.Axioms.Basic

notation "ℕ" => ω
notation "ℕ+" => Diff ω {ø}c

-- natural number
noncomputable def ClassSuccSet (x: SetType) : Class := x.1 ∪ {x}c
noncomputable def ClassSuccIsSet (x: SetType) : Set (ClassSuccSet x) := by {
  sorry;
}
noncomputable def ClassSucc (x: SetType) : SetType where
  X := ClassSuccSet x
  x := ClassSuccIsSet x

noncomputable def ClassSetTypeOfNat (n : Nat) : SetType :=
  match n with
    | 0     => ø_set
    | n + 1  => ClassSucc (ClassSetTypeOfNat n)
noncomputable def ClassSetOfNat (n : Nat) : Class := (ClassSetTypeOfNat n).1

noncomputable instance : OfNat Class n where
  ofNat := ClassSetOfNat n

