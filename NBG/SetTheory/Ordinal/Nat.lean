import NBG.SetTheory.Axioms.Basic

notation "ℕ" => ω
notation "ℕ+" => Diff ω {ø}

-- natural number
noncomputable def ClassSucc_mk (x: Class) [Set x] : Class := x ∪ {x}
noncomputable def ClassSuccIsSet (x: Class) [Set x] : Set (ClassSucc_mk x) := by {
  sorry;
}
noncomputable def ClassSuccSet (x: SetType) : SetType := by {
  sorry;
}

noncomputable def ClassSetTypeOfNat (n : Nat) : SetType :=
  match n with
    | 0     => SetType.mk ø EmptyClassIsSet
    | n + 1  => ClassSuccSet (ClassSetTypeOfNat n)
noncomputable def ClassSetOfNat (n : Nat) : Class := (ClassSetTypeOfNat n).1

noncomputable instance : OfNat Class n where
  ofNat := ClassSetOfNat n

