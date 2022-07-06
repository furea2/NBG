theorem IffNotNot {p: Prop}:
  p ↔ ¬ ¬ p := by {
  apply Iff.intro;
  {exact fun h hn => hn h;}
  {
    intro h;
    by_cases hp: p;
    {exact hp;}
    {exact False.elim (h hp);}
  }
}

theorem ImpIffNotImpNot {p q: Prop}:
  (p → q) ↔ (¬ q → ¬ p) := by {
  apply Iff.intro;
  {exact fun h hnq hp => hnq (h hp);}
  {
    intro h hp;
    by_cases hq: q;
    {exact hq;}
    {exact False.elim ((h hq) hp);}
  }
}
theorem IffIffNotIffNot {p q: Prop}:
  (p ↔ q) ↔ (¬ q ↔ ¬ p) := by {
  apply Iff.intro;
  {exact fun h => ⟨ImpIffNotImpNot.1 h.1,ImpIffNotImpNot.1 h.2⟩;}
  {exact fun h => ⟨ImpIffNotImpNot.2 h.1,ImpIffNotImpNot.2 h.2⟩;}
}

theorem NotExistsImpForall {α : Sort u} {p: α → Prop}:
  (¬ (∃a: α, p a)) → (∀a: α, ¬ p a) :=
fun h a ha => h (Exists.intro a ha)
theorem NotFoallImpExists {α : Sort u} {p: α → Prop}:
  ¬ (∀a: α, p a) → (∃a: α, ¬ p a) := by {
  intro h;
  by_cases ha : (∃a: α, ¬ p a);
  {exact ha;}
  {exact False.elim (h (fun a => IffNotNot.2 (NotExistsImpForall ha a)));}
}

theorem ExistsIffNotForall {α : Sort u} {p: α → Prop}:
  (¬ (∃a: α, p a)) ↔ (∀a: α, ¬ p a) := by {
  apply Iff.intro;
  {exact NotExistsImpForall;}
  {exact fun h ⟨a, pa⟩ => (h a) pa;}
}
theorem ForallIffNotExists {α : Sort u} {p: α → Prop}:
  ¬ (∀a: α, p a) ↔ (∃a: α, ¬ p a) := by {
  apply Iff.intro;
  {exact NotFoallImpExists;}
  {exact fun ⟨a, pa⟩ h => pa (h a);}
}

theorem NotOrIffNotAndNot {p q:Prop}:
  ¬ (p ∨ q) ↔ (¬ p) ∧ (¬ q) := by {
  apply Iff.intro;
  {
    intro h;
    by_cases hp:p;
    {exact False.elim (h (Or.inl hp));}
    {
      by_cases hq:q;
      {exact False.elim (h (Or.inr hq));}
      {exact (And.intro hp hq)}
    }
  }
  {
    intro h hn;
    cases hn;
    case mpr.inl hn => {exact h.1 hn}
    case mpr.inr hn => {exact h.2 hn}
  }
}


theorem NotAndIffNotOrNot {p q:Prop}:
  ¬ (p ∧ q) ↔ (¬ p) ∨ (¬ q) := by {
  apply Iff.intro;
  {
    intro h;
    by_cases hp:p;
    {
      by_cases hq:q;
      {exact False.elim (h (And.intro hp hq))}
      {exact Or.inr hq;}
    }
    {exact Or.inl hp;}
  }
  {
    intro h hn;
    cases h;
    case mpr.inl h => {exact h hn.1}
    case mpr.inr h => {exact h hn.2}
  }
}



