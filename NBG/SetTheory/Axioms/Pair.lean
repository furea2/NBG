import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Difference

open Classical

-- 4. AxiomPair
axiom AxiomPair :
  ∀x y: Class, Set x → Set y
    → ∃z: Class,
      (z∈U) ∧ (∀u: Class, (u∈z ↔ (u ＝ x ∨ u ＝ y)))
noncomputable def Pair_mk (X Y: Class) [hx: Set X] [hy: Set Y] : Class :=
  choose (AxiomPair X Y hx hy)
noncomputable def Pair_def (X Y: Class) [hx: Set X] [hy: Set Y] :=
  choose_spec (AxiomPair X Y hx hy)
noncomputable def Pair_is_Set (X Y: Class) [Set X] [Set Y] : Set (Pair_mk X Y) :=
  Set.mk₂ (Pair_def X Y).1

-- singleton def
theorem SingletonSetExists (X: Class) [hx: Set X]:
  ∃z: Class,
    (z∈U) ∧ (∀u: Class, (u∈z ↔ (u ＝ X))) := by {
  exists (Pair_mk X X);
  apply And.intro;
  {exact (Pair_is_Set X X).2;}
  {
    intro u;
    have h := (Pair_def X X).2 u;
    apply Iff.trans h;
    apply Iff.intro;
    {
      intro h;
      cases h;
      case mp.inl h => exact h;
      case mp.inr h => exact h;
    }
    {exact fun h => (Or.inl h);}
  }
}
noncomputable def Singleton_mk (X: Class) [Set X]: Class :=
  choose (SingletonSetExists X)
noncomputable def Singleton_def (X: Class) [Set X]:
  ((Singleton_mk X) ∈ U) ∧ (∀u: Class, (u ∈ (Singleton_mk X) ↔ (u ＝ X))) :=
  choose_spec (SingletonSetExists X)
noncomputable def Singleton_is_Set (X: Class) [Set X]: Set (Singleton_mk X) :=
  Set.mk₂ (Singleton_def X).1

notation "{"x"}" => Singleton_mk x
notation "{"x","y"}" => Pair_mk x y

def isSingleton (X : Class) :=
  ∃x: Class, ∀u: Class, u∈X ↔ u＝x
class Singleton (X : Class) :=
  isSingleton: isSingleton X
def isPair (X : Class) :=
  ∃x y: Class, ∀u: Class, u∈X ↔ u＝x ∨ u＝y
class Pair (X : Class) :=
  isPair: isPair X

-- ordered pair
noncomputable def OrdPair_mk (X Y: Class) [Set X] [Set Y] : Class :=
  @Pair_mk {X} {X, Y} (Singleton_is_Set X) (Pair_is_Set X Y)
noncomputable def OrdPair_def (X Y: Class) [Set X] [Set Y] :=
  @Pair_def {X} {X, Y} (Singleton_is_Set X) (Pair_is_Set X Y)
noncomputable def OrdPair_is_Set (X Y: Class) [Set X] [Set Y] : Set (OrdPair_mk X Y) :=
  @Pair_is_Set {X} {X, Y} (Singleton_is_Set X) (Pair_is_Set X Y)
notation "＜"x","y"＞" => OrdPair_mk x y

noncomputable def OrdTriple_mk (X Y Z: Class) [Set X] [Set Y] [Set Z] : Class :=
  @OrdPair_mk ＜X, Y＞ Z (OrdPair_is_Set X Y) _
noncomputable def OrdTriple_def (X Y Z: Class) [Set X] [Set Y] [Set Z] :=
  @OrdPair_def ＜X, Y＞ Z (OrdPair_is_Set X Y) _
noncomputable def OrdTriple_is_Set (X Y Z: Class) [Set X] [Set Y] [Set Z]: Set (OrdTriple_mk X Y Z) :=
  @OrdPair_is_Set ＜X, Y＞ Z (OrdPair_is_Set X Y) _

-- ordered triple
notation "＜"x","y","z"＞" => OrdTriple_mk x y z

-- singleton
theorem SingletonIntro (x: Class) [Set x]:
  ∀u: Class, (u ∈ (Singleton_mk x) ↔ u ＝ x) :=
  fun u => (Singleton_def x).2 u

theorem SingletonSingleton (x y: Class) [Set x] [Set y]:
  {x} ＝ {y} ↔ x ＝ y:= by {
  apply Iff.intro;
  {
    intro h;
    rw [AxiomExtensionality] at h;
    have hx := (h x);
    rw [SingletonIntro, SingletonIntro] at hx;
    exact hx.1 (ClassEq.refl x);
  }
  {
    intro h;
    rw [AxiomExtensionality];
    intro z;
    apply Iff.trans ((Singleton_def x).2 z);
    apply Iff.trans _ ((Singleton_def y).2 z).symm;
    apply Iff.intro;
    {exact fun h' => ClassEq.trans h' h;}
    {exact fun h' => ClassEq.trans h' (ClassEq.symm h);}
  }
}

-- pair
theorem PairIntro (X Y: Class) [Set X] [Set Y]:
  ∀u: Class, (u ∈ (Pair_mk X Y) ↔ (u ＝ X ∨ u ＝ Y)) := (Pair_def X Y).2

theorem PairSymm (x y: Class) [Set x] [Set y]:
  {x, y} ＝ {y, x} := by {
    rw [AxiomExtensionality];
    intro z;
    rw [PairIntro, PairIntro];
    apply Iff.intro;
    { 
      intro h;
      cases h;
      case mp.inl h => {exact Or.inr h;}
      case mp.inr h => {exact Or.inl h;}
    }
    {
      intro h;
      cases h;
      case mpr.inl h => {exact Or.inr h;}
      case mpr.inr h => {exact Or.inl h;}
    }
}

theorem SingletonEqSelfPair (x: Class) [Set x]:
  {x} ＝ {x, x} := by {
  rw [AxiomExtensionality];
  intro z;
  rw [SingletonIntro, PairIntro];
  apply Iff.intro;
  {exact fun h => Or.inr h;}
  {
    intro h;
    cases h;
    case mpr.inl h => {exact h;}
    case mpr.inr h => {exact h;}
  }
}

theorem SingletonPair {x y z: Class} [Set x] [Set y] [Set z]:
  {x} ＝ {y, z} ↔ x ＝ y ∧ x ＝ z:= by {
  apply Iff.intro;
  {
    intro h;
    rw [AxiomExtensionality] at h;
    have hy := h y;
    rw [SingletonIntro,PairIntro] at hy;
    have hy := ClassEq.symm (hy.2 (Or.inl (ClassEq.refl y)));
    have hz := h z;
    rw [SingletonIntro,PairIntro] at hz;
    have hz := ClassEq.symm (hz.2 (Or.inr (ClassEq.refl z)));
    exact ⟨hy,hz⟩;
  }
  {
    intro h;
    rw [AxiomExtensionality];
    intro u;
    rw [SingletonIntro,PairIntro];
    apply Iff.intro;
    {exact fun h'=> Or.inl (ClassEq.trans h' h.1);}
    {
      intro h';
      cases h';
      case mpr.mpr.inl h' => {exact ClassEq.trans h' (ClassEq.symm h.1);}
      case mpr.mpr.inr h' => {exact ClassEq.trans h' (ClassEq.symm h.2);}
    }
  }
}


-- -- ordered pair
theorem OrdPairIntro (x y: Class) [Set x] [Set y]:
  ∀u: Class, (u∈＜x, y＞ ↔ (u ＝ {x} ∨ u ＝ {x,y})) :=
  fun u => (@Pair_def {x} {x,y} (Singleton_is_Set x) (Pair_is_Set x y)).2 u

theorem OrdPairEq₁ {x y u v: Class} [Set x] [Set y] [Set u] [Set v]:
  (x ＝ u) →  (y ＝ v) → (＜x,y＞ ＝ ＜u,v＞) := by {
  intro h1 h2;
  rw [AxiomExtensionality];
  intro z;
  rw [OrdPairIntro,OrdPairIntro];
  apply Iff.intro;
  case mp => {
    intro h3;
    cases h3;
    case inl h3 => {
      rw [←SingletonSingleton] at h1;
      exact Or.inl (ClassEq.trans h3 h1);
    }
    case inr h3 => {
      apply Or.inr;
      apply ClassEq.trans h3;
      rw [AxiomExtensionality];
      intro z;
      rw [PairIntro, PairIntro];
      apply Iff.intro;
      {
        intro h;
        cases h;
        case h.mp.inl h => {exact Or.inl (ClassEq.trans h h1);}
        case h.mp.inr h => {exact Or.inr (ClassEq.trans h h2);}
      }
      {
        intro h;
        cases h;
        case h.mpr.inl h => {exact Or.inl (ClassEq.trans h (ClassEq.symm h1));}
        case h.mpr.inr h => {exact Or.inr (ClassEq.trans h (ClassEq.symm h2));}
      }
    }
  }
  case mpr => {
    intro h3;
    cases h3;
    case inl h3 => {
      rw [←SingletonSingleton] at h1;
      exact Or.inl (ClassEq.trans h3 (ClassEq.symm h1));
    }
    case inr h3 => {
      apply Or.inr;
      apply ClassEq.trans h3;
      rw [AxiomExtensionality];
      intro z;
      rw [PairIntro, PairIntro];
      apply Iff.intro;
      {
        intro h;
        cases h;
        case h.mp.inl h => {exact Or.inl (ClassEq.trans h (ClassEq.symm h1));}
        case h.mp.inr h => {exact Or.inr (ClassEq.trans h (ClassEq.symm h2));}
      }
      {
        intro h;
        cases h;
        case h.mpr.inl h => {exact Or.inl (ClassEq.trans h h1);}
        case h.mpr.inr h => {exact Or.inr (ClassEq.trans h h2);}
      }
    }
  }
}

theorem OrdPairEq₂ {x y: Class} [Set x] [Set y]:
  x ＝ y → (∀(z: Class), (z ＝ {x} ∨ z ＝ {x, y}) ↔ (z ＝ {x})) := by {
  intro h z;
  apply Iff.intro;
  {
    intro hz;
    cases hz;
    case mp.inl hz => {exact hz}
    case mp.inr hz => {
      apply ClassEq.trans hz;
      rw [AxiomExtensionality];
      intro z;
      rw [SingletonIntro, PairIntro];
      apply Iff.intro;
      case mp => {
        intro h';
        cases h';
        case inl h' => {exact h';}
        case inr h' => {exact ClassEq.trans h' (ClassEq.symm h);}
      }
      case mpr => {exact fun h => Or.inl h;}
    }
  }
  {exact fun hz => Or.inl hz;}
}

theorem OrdPairEq {x y u v: Class} [Set x] [Set y] [Set u] [Set v]:
  (＜x,y＞ ＝ ＜u,v＞) ↔ (x ＝ u ∧ y ＝ v) := by {
  apply Iff.intro;
  {
    intro h;
    rw [AxiomExtensionality] at h;
    have h : ∀(z: Class),
      (z ＝ {x} ∨ z ＝ {x,y}) ↔ (z ＝ {u} ∨ z ＝ {u,v}) := by {
      intro z;
      rw [←OrdPairIntro,←OrdPairIntro];
      exact h z;
    };
    by_cases hxu : (x ＝ u);
    {
      have hyv : (y ＝ v) := by {
        by_cases hxy : (x ＝ y);
        {
          have h : ∀(z: Class), (z ＝ {u} ∨ z ＝ {u,v}) ↔ (z ＝ {x}) :=
            fun z => (Iff.trans (h z).symm (OrdPairEq₂ hxy z));
          have h' := ClassEq.symm ((h {u, v}).1 (Or.inr (ClassEq.refl {u,v})));
          rw [SingletonPair] at h';
          exact ClassEq.trans (ClassEq.symm hxy) h'.2;
        }
        {
          have h' := (h {x,y}).1 (Or.inr (ClassEq.refl {x,y}));
          cases h';
          case inr.inl h' => {
            have h' := SingletonPair.1 (ClassEq.symm h');
            have hxy' := ClassEq.trans (ClassEq.symm h'.1) h'.2;
            contradiction;
          }
          case inr.inr h' => {
            rw [AxiomExtensionality] at h';
            have hy := h' y;
            rw [PairIntro, PairIntro] at hy;
            have hy := hy.1 (Or.inr (ClassEq.refl y));
            cases hy;
            case inl hy => {
              have hxy' := ClassEq.trans hxu (ClassEq.symm hy);
              contradiction;
            }
            case inr hy => {exact hy;}
          }
        }
      }
      exact ⟨hxu, hyv⟩;
    }
    {
      have hx := (h {x}).1 (Or.inl (ClassEq.refl _));
      cases hx;
      case mp.inr.inl hx => {
        rw [SingletonSingleton] at hx;
        contradiction;
      }
      case mp.inr.inr hx => {
        rw [SingletonPair] at hx;
        have := hx.1;
        contradiction;
      }
    }
  }
  {exact fun h => OrdPairEq₁ h.1 h.2;}
}

theorem OrdTripleEq {x y z u v w: Class} [Set x] [Set y] [Set z] [Set u] [Set v] [Set w]:
  (＜x,y,z＞ ＝ ＜u,v,w＞) ↔ (x ＝ u ∧ y ＝ v ∧ z ＝ w) := by {
  have hxy := OrdPair_is_Set x y;
  have huv := OrdPair_is_Set u v;
  have h1 := @OrdPairEq ＜x, y＞ z ＜u,v＞ w;
  have h2 := @OrdPairEq x y u v;
  apply Iff.trans h1;
  rw [h2];
  apply Iff.intro;
  {exact fun h => ⟨h.1.1,⟨h.1.2,h.2⟩⟩;}
  {exact fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩}
}
