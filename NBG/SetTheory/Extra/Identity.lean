import NBG.SetTheory.Axioms.Basic

open Classical

-- subset function
theorem SubsetInductiveClassExists:
  ∃S: Class, ∀z:Class,
    (z ∈ S ↔ ∃x y: Class, ∃_: Set x, ∃_: Set y, ∃_: x ⊂ y,
      z ＝ ＜x, y＞) := by {
  sorry;
}

noncomputable def S : Class :=
  choose SubsetInductiveClassExists
noncomputable def S_def :=
  choose_spec SubsetInductiveClassExists

theorem SubsetPairAreInS {x y: Class} [hx: Set x] [hy: Set y]:
  x ⊂ y → ＜x, y＞ ∈ S :=
fun h =>  (S_def ＜x, y＞).2 ⟨x, ⟨y, ⟨hx, ⟨hy, ⟨h, ClassEq.refl _⟩⟩⟩⟩⟩

-- identity function
theorem IdentityFunctionExists:
  ∃Id: Class, ∀z:Class,
    (z ∈ Id ↔ ∃x: Class, ∃_: Set x, z ＝ ＜x, x＞) := by {
  sorry;
}

noncomputable def IdClass : Class :=
  choose IdentityFunctionExists
noncomputable def IdClass_def :=
  choose_spec IdentityFunctionExists

theorem AllIdSetIsInId (x: Class) [hx: Set x]:
  ＜x, x＞ ∈ IdClass :=
(IdClass_def ＜x, x＞).2 ⟨x, ⟨hx, ClassEq.refl _⟩⟩



