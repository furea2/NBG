import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Differrence

open Classical

-- 4. AxiomPair
axiom AxiomPair :
  ∀x y: Class, x ∈ U → y ∈ U
    → ∃z: Class,
      (z∈U) ∧ (∀u: Class, (u∈z ↔ (u ＝ x ∧ u ＝ y)))
noncomputable def Pair (x y: Class) (hx: x∈ U) (hy: y∈ U) : Class :=
choose (AxiomPair x y hx hy)
noncomputable def Pair_def (x y: Class) (hx: x∈ U) (hy: y∈ U) :=
choose_spec (AxiomPair x y hx hy)

noncomputable def PairSet_def (x y: Set) := Pair_def x.1 y.1 (SetInU x) (SetInU y)
noncomputable def PairSet (x y: Set) : Set :=
⟨Pair x.1 y.1 (SetInU x) (SetInU y), AllSetInU.2 (PairSet_def x y).1⟩

-- variable (x : Class) (hx : x ∈ U)
notation "{"x"}" => PairSet x x
notation "{"x","y"}" => PairSet x y
noncomputable def OrdPair (x y: Set) := {{x}, {x, y}}
notation "＜"x","y"＞" => OrdPair x y
notation "＜"x","y","z"＞" => OrdPair (OrdPair x y) z

theorem PairIntro (x y: Set):
  ∀u: Class, (u∈(PairSet x y).1 ↔ (u ＝ x.1 ∧ u ＝ y.1)) := (PairSet_def x y).2

def isSingleton (X : Class) :=
  ∃x: Class, ∀u: Class, u∈X ↔ u＝x
class Singleton where
  α : Class
  isSingleton : isSingleton α

theorem SingletonIntro (x : Set):
  ∀u: Class, u∈(PairSet x x).1 ↔ u＝x.1 := by {
  intro u;
  rw [PairIntro];
  apply Iff.intro;
  {exact fun h => h.1;}
  {exact fun h => ⟨h,h⟩;}
}

theorem SingletonSingleton (x y : Class) [Set x] [Set y]:
  {x} ＝ {y} → x ＝ y:= by {
  intro h;
  rw [AxiomExtensionality] at h;
  have hx := h x;
  rw [SingletonIntro,SingletonIntro] at hx;
  rw [←hx];
  exact ClassEqRefl x;
}

theorem PairSymm (x y: Class) [Set x] [Set y] :
  {x,y} ＝ {y,x} := by {
    rw [AxiomExtensionality];
    intro z;
    rw [PairIntro, PairIntro];
    apply Iff.intro;
    {exact fun h => ⟨h.right,h.left⟩;}
    {exact fun h => ⟨h.right,h.left⟩;}
}

theorem PairEq (x y u v: Class) [Set x] [Set y] [Set u] [Set v]:
  (＜x,y＞ ＝ ＜u,v＞) ↔ (x ＝ u ∧ y ＝ v) := by {
  sorry;
}


