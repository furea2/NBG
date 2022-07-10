import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Inversion

open Classical

-- 7. AxiomDomain
axiom AxiomDomain :
  ∀X: Class, ∃D: Class,
    ∀z: Class,
      (z∈D ↔ (∃x: Class, ∃_: Set x, ∃y: Class, ∃_: Set y,
        ∃_:＜x, y＞ ∈ X, (z ＝ x)))

-- domain
noncomputable def Dom (X: Class): Class :=
  choose (AxiomDomain X)
noncomputable def Dom_def (X: Class):
  ∀z: Class,
    (z∈(Dom X) ↔ (∃x: Class, ∃_: Set x, ∃y: Class, ∃_: Set y,
      ∃_:＜x, y＞ ∈ X, (z ＝ x))) :=
  choose_spec (AxiomDomain X)

-- rangle
noncomputable def Rng (X: Class) [Relation X]: Class :=
  choose (AxiomDomain (RelInv X))
noncomputable def Rng_def' (X: Class) [Relation X]:
  ∀z: Class,
    (z∈(Dom (RelInv X)) ↔ (∃x: Class, ∃_: Set x, ∃y: Class, ∃_: Set y,
      ∃_:＜x, y＞ ∈ (RelInv X), (z ＝ x))) :=
  choose_spec (AxiomDomain (RelInv X))
noncomputable def Rng_def (X: Class) [Relation X]:
  ∀z: Class,
    (z∈(Dom X) ↔ (∃x: Class, ∃_: Set x, ∃y: Class, ∃_: Set y,
      ∃_:＜x, y＞ ∈ X, (z ＝ y))) := sorry

