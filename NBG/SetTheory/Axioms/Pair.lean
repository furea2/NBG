import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Differrence

open Classical

-- 4. AxiomPair
axiom AxiomPair :
  ∀x y: Class, x ∈ U → y ∈ U
    → ∃Z: Class,
      (Z∈U) ∧ (∀u: Class, (u∈Z ↔ (u ＝ x ∧ u ＝ y)))
noncomputable def Pair (X Y: Class) [hx: Set X] [hy: Set Y] : Class :=
  choose (AxiomPair X Y hx.2 hy.2)
noncomputable def Pair_def (X Y: Class) [hx: Set X] [hy: Set Y] :=
  choose_spec (AxiomPair X Y hx.2 hy.2)
noncomputable def Pair' (X Y: Class) (hx: X ∈ U) (hy: Y∈ U) : Class :=
  choose (AxiomPair X Y hx hy)
noncomputable def Pair_def' (X Y: Class) (hx: X ∈ U) (hy: Y∈ U) :=
  choose_spec (AxiomPair X Y hx hy)
noncomputable def PairSet_def (_: Set X) (_: Set Y) :=
  (Pair_def X Y)
noncomputable def PairSet (x: Set X) (y: Set Y) : Set (Pair X Y) := {
  isSet := AllSetInU.2 (PairSet_def x y).1,
  inU   := (PairSet_def x y).1
}
theorem SingletonExists (x: Class) [hx: Set x]:
  ∃z: Class,
    ((z∈U) ∧ (∀u: Class, (u∈z ↔ (u ＝ x)) )) := by {
  exists (Pair x x);
  have ⟨h1, h2⟩ := Pair_def x x;
  apply And.intro;
  {exact h1;}
  {
    intro z;
    apply Iff.intro;
    {exact fun h => ((h2 z).1 h).1}
    {exact fun h => ((h2 z).2 ⟨h, h⟩)}
  }
}

noncomputable def Singleton (x: Class) [Set x] : Class :=
  choose (SingletonExists x)
noncomputable def Singleton_def (x: Class) [Set x] :=
  choose_spec (SingletonExists x)
noncomputable def SingletonSet_def (x: Class) [Set x] :=
  (Singleton_def x)
noncomputable def SingletonSet (x: Class) [Set x] : Set (Singleton x) := {
  isSet := AllSetInU.2 (Singleton_def x).1,
  inU   := (Singleton_def x).1,
}

notation "{"x"}c" => Singleton x
notation "{"x","y"}c" => Pair x y
-- notation "{"x"}s" => SingletonSet x
notation "{"x"}s" => PairSet x x
notation "{"x","y"}s" => PairSet x y
noncomputable def OrdPair (X Y: Class) [hx: Set X] [hy: Set Y] : Class :=
@Pair {X}c {X, Y}c (SingletonSet X) (PairSet hx hy)
noncomputable def OrdPair_def (X Y: Class) [hx: Set X] [hy: Set Y] :=
@Pair_def {X}c {X, Y}c (SingletonSet X) (PairSet hx hy)
noncomputable def OrdPair' (X Y: Class) (hx: X ∈ U) (hy: Y ∈ U) : Class :=
Pair' (Pair' X X hx hx) (Pair' X Y hx hy) (Pair_def' X X hx hx).1 (Pair_def' X Y hx hy).1
noncomputable def OrdPair_def' (X Y: Class) (hx: X ∈ U) (hy: Y ∈ U) :=
Pair_def' (Pair' X X hx hx) (Pair' X Y hx hy) (Pair_def' X X hx hx).1 (Pair_def' X Y hx hy).1
noncomputable def OrdPairSet (x: Set X) (y: Set Y) := {{x}s, {x, y}s}s
notation "＜"x","y"＞c" => OrdPair x y
notation "＜"x","y","z"＞c" => OrdPair (OrdPair x y) z
notation "＜"x","y"＞s" => OrdPairSet x y
notation "＜"x","y","z"＞s" => OrdPairSet (OrdPairSet x y) z

theorem PairIntro (x y: Class) [Set x] [Set y] :
  ∀u: Class, (u∈{x, y}c ↔ (u ＝ x ∧ u ＝ y)) := (Pair_def x y).2

def isSingleton (X : Class) :=
  ∃x: Class, ∀u: Class, u∈X ↔ u＝x

theorem SingletonIntro (x : Class) [Set x]:
  ∀u: Class, u∈{x}c ↔ u＝x := fun u => (Singleton_def x).2 u

theorem SingletonSingleton (x y : Class) [Set x] [Set y]:
  {x}c ＝ {y}c ↔ x ＝ y:= by {
  apply Iff.intro;
  {
    intro h;
    rw [AxiomExtensionality] at h;
    have hx := h x;
    rw [SingletonIntro,SingletonIntro] at hx;
    rw [←hx];
    exact ClassEqRefl x;
  }
  {
    intro h;
    rw [AxiomExtensionality];
    intro z;
    apply Iff.trans ((Singleton_def x).2 z);
    apply Iff.trans _ ((Singleton_def y).2 z).symm;
    apply Iff.intro;
    {exact fun h' => ClassEqTrans h' h;}
    {exact fun h' => ClassEqTrans h' (ClassEqSymm h);}
  }
}

theorem PairSymm (x y: Class) [Set x] [Set y] :
  {x, y}c ＝ {y, x}c := by {
    rw [AxiomExtensionality];
    intro z;
    rw [PairIntro, PairIntro];
    apply Iff.intro;
    {exact fun h => ⟨h.right,h.left⟩;}
    {exact fun h => ⟨h.right,h.left⟩;}
}

private theorem PairEq₁ {x y u v: Class} [Set x] [Set y] [Set u] [Set v]:
  (x ＝ u) →  (y ＝ v) → (＜x,y＞c ＝ ＜u,v＞c) := sorry

theorem PairEq {x y u v: Class} [Set x] [Set y] [Set u] [Set v]:
  (＜x,y＞c ＝ ＜u,v＞c) ↔ (x ＝ u ∧ y ＝ v) := by {
  apply Iff.intro;
  {sorry;}
  {exact fun h => PairEq₁ h.1 h.2;}
}

