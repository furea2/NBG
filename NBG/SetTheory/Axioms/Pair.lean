import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Differrence

open Classical

-- 4. AxiomPair
axiom AxiomPair :
  ∀x y: Class, x ∈ U → y ∈ U
    → ∃Z: Class,
      (Z∈U) ∧ (∀u: Class, (u∈Z ↔ (u ＝ x ∨ u ＝ y)))
-- noncomputable def Pair (X Y: Class) [hx: Set X] [hy: Set Y] : Class :=
--   (choose (AxiomPair X Y hx.2 hy.2))
noncomputable def Pair (x y: SetType) : Class :=
  (SetType.mk₂ ((choose (AxiomPair x.1 y.1 x.2.2 y.2.2))) ((choose_spec (AxiomPair x.1 y.1 x.2.2 y.2.2))).1).1
noncomputable def Pair_def (x y: SetType) :=
  choose_spec (AxiomPair x.1 y.1 x.2.2 y.2.2)
noncomputable def PairSet (x y: SetType) : SetType :=
  (SetType.mk₂ ((choose (AxiomPair x.1 y.1 x.2.2 y.2.2))) ((choose_spec (AxiomPair x.1 y.1 x.2.2 y.2.2))).1)

-- singleton def
theorem SingletonSetExists (x: SetType):
  ∃z: SetType,
    (∀u: Class, (u∈z.1 ↔ (u ＝ x.1)) ) := by {
  exists (PairSet x x);
  intro u;
  have h := (Pair_def x x).2 u;
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
noncomputable def Singleton (x: SetType) : Class :=
  (choose (SingletonSetExists x)).1
noncomputable def Singleton_def (x: SetType) :=
  choose_spec (SingletonSetExists x)
noncomputable def SingletonSet (x: SetType) : SetType :=
  choose (SingletonSetExists x)

notation "{"x"}c" => Singleton x
notation "{"x","y"}c" => Pair x y
notation "{"x"}s" => SingletonSet x
notation "{"x","y"}s" => PairSet x y


-- ordered pair
noncomputable def OrdPair (x y: SetType) : Class := { {x}s , {x, y}s }c
noncomputable def OrdPair_def (x y: SetType) := Pair_def {x}s {x, y}s
noncomputable def OrdPairSet (x y: SetType) : SetType := PairSet {x}s {x, y}s
notation "＜"x","y"＞c" => OrdPair x y
notation "＜"x","y"＞s" => OrdPairSet x y

noncomputable def OrdTriple (x y z: SetType) : Class := ＜＜x, y＞s, z＞s.1
noncomputable def OrdTriple_def (x y z: SetType) := OrdPair_def ＜x, y＞s z
noncomputable def OrdTripleSet (x y z: SetType): SetType := ＜＜x, y＞s, z＞s

-- ordered triple
notation "＜"x","y","z"＞c" => ＜＜x, y＞s, z＞s.1
notation "＜"x","y","z"＞s" => ＜＜x, y＞s, z＞s

-- singleton
def isSingleton (X : Class) :=
  ∃x: Class, ∀u: Class, u∈X ↔ u＝x

theorem SingletonIntro (x : SetType):
  ∀u: Class, u∈{x}c ↔ u＝x.1 := fun u => (Singleton_def x) u

theorem SingletonSingleton {x y : SetType}:
  {x}c ＝ {y}c ↔ x.1 ＝ y.1:= by {
  apply Iff.intro;
  {
    intro h;
    rw [AxiomExtensionality] at h;
    have hx := h x.1;
    rw [SingletonIntro,SingletonIntro] at hx;
    rw [←hx];
    exact ClassEq.refl x.1;
  }
  {
    intro h;
    rw [AxiomExtensionality];
    intro z;
    apply Iff.trans ((Singleton_def x) z);
    apply Iff.trans _ ((Singleton_def y) z).symm;
    apply Iff.intro;
    {exact fun h' => ClassEq.trans h' h;}
    {exact fun h' => ClassEq.trans h' (ClassEq.symm h);}
  }
}

-- pair
theorem PairIntro (x y: SetType):
  ∀u: Class, (u∈{x, y}c ↔ (u ＝ x.1 ∨ u ＝ y.1)) := (Pair_def x y).2

theorem PairSymm {x y: SetType}:
  {x, y}c ＝ {y, x}c := by {
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

theorem SingletonEqSelfPair {x: SetType}:
  {x}c ＝ {x, x}c := by {
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

theorem SingletonPair {x y z : SetType}:
  {x}c ＝ {y, z}c ↔ x ＝ y ∧ x ＝ z:= by {
  apply Iff.intro;
  {
    intro h;
    rw [AxiomExtensionality] at h;
    have hy := h y.1;
    rw [SingletonIntro,PairIntro] at hy;
    have hy := ClassEq.symm (hy.2 (Or.inl (ClassEq.refl y.1)));
    have hz := h z.1;
    rw [SingletonIntro,PairIntro] at hz;
    have hz := ClassEq.symm (hz.2 (Or.inr (ClassEq.refl z.1)));
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
theorem OrdPairIntro (x y: SetType):
  ∀u: Class, (u∈＜x, y＞c ↔ (u ＝ {x}c ∨ u ＝ {x,y}c)) :=
  fun u => (PairIntro {x}s {x,y}s) u

theorem OrdPairEq₁ {x y u v: SetType}:
  (x.1 ＝ u.1) →  (y.1 ＝ v.1) → (＜x,y＞c ＝ ＜u,v＞c) := by {
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
      rw [PairIntro,PairIntro];
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
      rw [PairIntro,PairIntro];
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

theorem OrdPairEq₂ {x y : SetType}:
  x ＝ y → (∀(z: Class), (z ＝ {x}c ∨ z ＝ {x, y}c) ↔ (z ＝ {x}c)) := by {
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
      rw [PairIntro,SingletonIntro];
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

theorem OrdPairEq {x y u v: SetType}:
  (＜x,y＞c ＝ ＜u,v＞c) ↔ (x.1 ＝ u.1 ∧ y.1 ＝ v.1) := by {
  apply Iff.intro;
  {
    intro h;
    rw [AxiomExtensionality] at h;
    have h : ∀(z: Class),
      (z ＝ {x}c ∨ z ＝ {x,y}c) ↔ (z ＝ {u}c ∨ z ＝ {u,v}c) := by {
      intro z;
      rw [←OrdPairIntro,←OrdPairIntro];
      exact h z;
    };
    by_cases hxu : (x ＝ u);
    {
      have hyv : (y ＝ v) := by {
        by_cases hxy : (x ＝ y);
        {
          have h : ∀(z: Class), (z ＝ {u}c ∨ z ＝ {u,v}c) ↔ (z ＝ {x}c) :=
            fun z => (Iff.trans (h z).symm (OrdPairEq₂ hxy z));
          have h' := ClassEq.symm ((h {u, v}c).1 (Or.inr (ClassEq.refl {u,v}c)));
          rw [SingletonPair] at h';
          exact ClassEq.trans (ClassEq.symm hxy) h'.2;
        }
        {
          have h' := (h {x,y}c).1 (Or.inr (ClassEq.refl {x,y}c));
          cases h';
          case inr.inl h' => {
            have h' := SingletonPair.1 (ClassEq.symm h');
            have hxy' := ClassEq.trans (ClassEq.symm h'.1) h'.2;
            contradiction;
          }
          case inr.inr h' => {
            rw [AxiomExtensionality] at h';
            have hy := h' y.1;
            rw [PairIntro,PairIntro] at hy;
            have hy := hy.1 (Or.inr (ClassEq.refl y.1));
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
      have hx := (h {x}c).1 (Or.inl (ClassEq.refl _));
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

theorem OrdTripleSetEq {x y z u v w: SetType}:
  (＜x,y,z＞s.1 ＝ ＜u,v,w＞s.1) ↔ (x.1 ＝ u.1 ∧ y.1 ＝ v.1 ∧ z.1 ＝ w.1) := by {
  -- unfold OrdTriple;
  have hxy := ＜x, y＞s;
  have huv := ＜u, v＞s;
  have h1 := @OrdPairEq ＜x, y＞s z ＜u,v＞s w;
  -- have h2 := @OrdPairEq x y u v;
  apply Iff.trans h1;
  -- rw [h2];
  -- apply Iff.intro;
  -- {exact fun h => ⟨h.1.1,⟨h.1.2,h.2⟩⟩;}
  -- {exact fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩}
  sorry;
}
