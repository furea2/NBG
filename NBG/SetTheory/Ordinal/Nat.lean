import NBG.SetTheory.Axioms.Basic

notation "ℕ" => ω
notation "ℕ+" => Diff ω {ø}c

-- natural number
noncomputable def ClassSucc (x: Class) [Set x] : Class := x ∪ {x}c
theorem ClassSuccInU (x: Class) [Set x] : (ClassSucc x) ∈ U := by {
  sorry;
  -- x ∪ {x}c
}
noncomputable def ClassSucc' (x: Class) [Set x] : Set (ClassSucc x) := {
  isSet := AllSetInU.2 (ClassSuccInU x),
  inU   := ClassSuccInU x
}

-- noncomputable def ClassOfNat (n : Nat): Class :=
--   match n with
--     | 0     => ø
--     | n + 1  => @ClassSucc (ClassOfNat n)

-- noncomputable instance : OfNat Class n where
--   ofNat := ClassOfNat n

