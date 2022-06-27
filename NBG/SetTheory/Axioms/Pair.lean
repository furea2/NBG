import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Differrence

open Classical

-- 4. AxiomPair
axiom AxiomPair :
  ∀X Y: Class, ∃Z: Class,
    ∀u: Class, (u∈Z ↔ (u ＝ X ∧ u ＝ Y))
noncomputable def Pair (X Y: Class) := choose (AxiomPair X Y)
noncomputable def Pair_def (X Y: Class) := choose_spec (AxiomPair X Y)
notation "{"x"}" => Pair x x
notation "{"x","y"}" => Pair x y
noncomputable def OrdPair (x y: Class) := {{x}, {x, y}}
notation "＜"x","y"＞" => OrdPair x y
notation "＜"x","y","z"＞" => OrdPair (OrdPair x y) z

theorem PairIntro (x y: Class) [Set x] [Set y] :
  ∀u: Class, (u∈Pair x y ↔ (u ＝ x ∧ u ＝ y)) := Pair_def x y

def isSingleton (X : Class) :=
  ∃x: Class, ∀u: Class, u∈X ↔ u＝x
class Singleton where
  α : Class
  isSingleton : isSingleton α

theorem SingletonIntro (x : Class) [Set x]:
  ∀u: Class, u∈Pair x x ↔ u＝x := by {
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


