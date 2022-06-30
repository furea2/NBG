import NBG.SetTheory.Defs
import NBG.SetTheory.Axioms.Differrence

open Classical

-- 4. AxiomPair
axiom AxiomPair :
  ∀x y: Class, x ∈ U → y ∈ U
    → ∃Z: Class,
      (Z∈U) ∧ (∀u: Class, (u∈Z ↔ (u ＝ x ∨ u ＝ y)))
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
    {
      intro h;
      have := ((h2 z).1 h);
      cases this;
      case right.mp.inl h => exact h;
      case right.mp.inr h => exact h;
    }
    {exact fun h => ((h2 z).2) (Or.inl h);}
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


-- singleton
def isSingleton (X : Class) :=
  ∃x: Class, ∀u: Class, u∈X ↔ u＝x

theorem SingletonIntro (x : Class) [Set x]:
  ∀u: Class, u∈{x}c ↔ u＝x := fun u => (Singleton_def x).2 u

theorem SingletonSingleton {x y : Class} [Set x] [Set y]:
  {x}c ＝ {y}c ↔ x ＝ y:= by {
  apply Iff.intro;
  {
    intro h;
    rw [AxiomExtensionality] at h;
    have hx := h x;
    rw [SingletonIntro,SingletonIntro] at hx;
    rw [←hx];
    exact ClassEq.refl x;
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
theorem PairIntro (x y: Class) [Set x] [Set y] :
  ∀u: Class, (u∈{x, y}c ↔ (u ＝ x ∨ u ＝ y)) := (Pair_def x y).2

theorem PairSymm {x y: Class} [Set x] [Set y] :
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

theorem SingletonEqSelfPair {x: Class} [Set x]:
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

theorem SingletonPair {x y z : Class} [Set x] [Set y] [Set z]:
  {x}c ＝ {y, z}c ↔ x ＝ y ∧ x ＝ z:= by {
  apply Iff.intro;
  {
    rw [];
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


-- ordered pair
theorem OrdPairIntro (x y: Class) [Set x] [Set y] :
  ∀u: Class, (u∈＜x, y＞c ↔ (u ＝ {x}c ∨ u ＝ {x,y}c)) := (OrdPair_def x y).2

theorem OrdPairEq₁ {x y u v: Class} [Set x] [Set y] [Set u] [Set v]:
  (x ＝ u) →  (y ＝ v) → (＜x,y＞c ＝ ＜u,v＞c) := by {
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

theorem OrdPairEq₂ {x y : Class} [Set x] [Set y]:
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

theorem OrdPairEq {x y u v: Class} [Set x] [Set y] [Set u] [Set v]:
  (＜x,y＞c ＝ ＜u,v＞c) ↔ (x ＝ u ∧ y ＝ v) := by {
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
            have hy := h' y;
            rw [PairIntro,PairIntro] at hy;
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

