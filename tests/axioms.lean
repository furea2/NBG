open Classical

universe u
variable (α : Type u)

class HasEq (α : Type u) where
  Eq : α → α → Prop
infix:50 " ＝ "  => HasEq.Eq

class HasIn (α : Type u) where
  In : α → α → Prop
infix:50 " ∈ "  => HasIn.In

class HasSubset (α : Type u) where
  Subset : α → α → Prop
infix:50 " ⊂ "  => HasSubset.Subset
infix:50 " ⊆ "  => HasSubset.Subset

class HasUnion (α : Type u) where
  Union : α → α → α
infix:50 " ∪ "  => HasUnion.Union

class HasInter (α : Type u) where
  Inter : α → α → α
infix:50 " ∩ "  => HasInter.Inter

class HasUnionAll (α : Type u) where
  UnionAll : α → α
notation " ⋃ "  => HasUnionAll.UnionAll

class HasInterAll (α : Type u) where
  InterAll : α → α
notation " ⋂ "  => HasInterAll.InterAll

class HasProduct (α : Type u) where
  Product : α → α → α
infix:50 " ✕ "  => HasProduct.Product

class HasPow  (α : Sort u) where
  Pow : α → α
notation "𝒫" => HasPow.Pow

class HasDiff  (α : Type u) where
  Diff : α → α → α
infix:50 " ＼ "  => HasDiff.Diff

axiom Class : Type u
axiom Class.In : Class → Class → Prop
axiom Class.Eq : Class → Class → Prop

instance : HasEq Class where
  Eq := Class.Eq
notation:50 X " ≠ " Y => ¬ (X ＝ Y)

instance : HasIn Class where
  In := Class.In
notation:50 X " ∉ " Y => ¬ X ∈ Y

def isSet (X : Class) : Prop := ∃(Y:Class), X ∈ Y

def isProper (X : Class) : Prop := ¬ (isSet X)
class ProperClass (X : Class) where
  isProper : isProper X

-- 1. AxiomExtensionality
axiom AxiomExtensionality :
  ∀X Y: Class, (X＝Y ↔ ∀z, (z ∈ X ↔ z ∈ Y))

def ClassSubset (X Y : Class) : Prop :=
  ∀z:Class, z ∈ X → z ∈ Y
instance : HasSubset Class where
  Subset := ClassSubset

-- 2. AxiomUniverse
axiom AxiomUniverse :
  ∃U : Class, ∀x: Class, (x∈U ↔ ∃X: Class,(x∈X))
noncomputable def U: Class :=
  choose AxiomUniverse

-- Set Type
theorem AllSetInU {x : Class}: isSet x ↔ x∈U := by {
  apply Iff.intro;
  {exact fun ⟨y, h⟩ => (choose_spec AxiomUniverse x).2 ⟨y, h⟩;}
  {exact fun h => (choose_spec AxiomUniverse x).1 h;}
}

class Set (X : Class) where
  isSet : isSet X
  inU   : X ∈ U
def Set.mk₁ {X Y: Class} (h: X ∈ Y): Set X :=
  Set.mk ⟨Y, h⟩ (AllSetInU.1 ⟨Y, h⟩)
def Set.mk₂ {X: Class} (hx: X ∈ U): Set X :=
  Set.mk (AllSetInU.2 hx) hx

-- 3. AxiomDifference
axiom AxiomDifference :
  ∀X Y: Class, ∃Z: Class,
    ∀u: Class, (u∈Z ↔ (u ∈ X ∧ u ∉ Y))
noncomputable def Diff (X Y: Class): Class :=
  choose (AxiomDifference X Y)
noncomputable instance : HasDiff Class where
  Diff := Diff

-- intersection
noncomputable def IntersectionClass_mk' (X Y: Class) :=
  X ＼ (X ＼ Y)
theorem IntersectionClassExists:
  ∀X Y: Class, ∃Z: Class,
    ∀z: Class, ((z ∈ Z) ↔ (z ∈ X) ∧ (z ∈ Y)) := by {
  intro X Y;
  let inter :=  X ＼ (X ＼ Y);
  sorry;
}
noncomputable def IntersectionClass_mk (X Y: Class) :=
  choose (IntersectionClassExists X Y)
noncomputable instance : HasInter Class where
  Inter := IntersectionClass_mk

-- union
theorem UnionClassExists:
  ∀X Y: Class, ∃Z: Class,
    ∀z: Class, ((z ∈ Z) ↔ (z ∈ X) ∨ (z ∈ Y)) := by {
  intro X Y;
  let union := U ＼ ((U ＼ X) ∩ (U ＼ Y));
  sorry;
}
noncomputable def UnionClass_mk (X Y: Class) :=
  choose (UnionClassExists X Y)
noncomputable instance : HasUnion Class where
  Union := UnionClass_mk

-- empty class
noncomputable def EmptyClass_mk' : Class :=
  U ＼ U
theorem EmptyClassExists:
  ∃Z: Class, ∀u: Class, (¬ u ∈ Z) := by {
  let emp := EmptyClass_mk';
  exists emp;
  sorry;
}
noncomputable def EmptyClass_mk : Class :=
  choose EmptyClassExists
notation " ø " => EmptyClass_mk

-- 4. AxiomPair
axiom AxiomPair :
  ∀x y: Class, x ∈ U → y ∈ U
    → ∃z: Class,
      (z∈U) ∧ (∀u: Class, (u∈z ↔ (u ＝ x ∨ u ＝ y)))
noncomputable def Pair_mk (X Y: Class) [hx: Set X] [hy: Set Y] : Class :=
  choose (AxiomPair X Y hx.2 hy.2)
noncomputable def Pair_def (X Y: Class) [hx: Set X] [hy: Set Y] :=
  choose_spec (AxiomPair X Y hx.2 hy.2)
noncomputable def Pair_is_Set (X Y: Class) [Set X] [Set Y] : Set (Pair_mk X Y) :=
  Set.mk₂ (Pair_def X Y).1
notation "{"x","y"}" => Pair_mk x y
notation "{"x","y"}s" => Pair_is_Set x y

-- singleton def
theorem SingletonSetExists (X: Class) [hx: Set X]:
  ∃z: Class,
    (z∈U) ∧ (∀u: Class, (u∈z ↔ (u ＝ X))) := by {
  exists (Pair_mk X X);
  sorry;
}
noncomputable def Singleton_mk (X: Class) [Set X]: Class :=
  choose (SingletonSetExists X)
noncomputable def Singleton_def (X: Class) [Set X]:
  ((Singleton_mk X) ∈ U) ∧ (∀u: Class, (u ∈ (Singleton_mk X) ↔ (u ＝ X))) :=
  choose_spec (SingletonSetExists X)
noncomputable def Singleton_is_Set (X: Class) [Set X]: Set (Singleton_mk X) :=
  Set.mk₂ (Singleton_def X).1
notation "{"x"}" => Singleton_mk x
notation "{"x"}s" => Singleton_is_Set x

-- ordered pair
noncomputable def OrdPair_mk (X Y: Class) [Set X] [Set Y] : Class :=
  @Pair_mk {X} {X, Y} {X}s {X, Y}s
noncomputable def OrdPair_def (X Y: Class) [Set X] [Set Y] :=
  @Pair_def {X} {X, Y} {X}s {X, Y}s
noncomputable def OrdPair_is_Set (X Y: Class) [Set X] [Set Y] : Set (OrdPair_mk X Y) :=
  @Pair_is_Set {X} {X, Y} {X}s {X, Y}s
notation "＜"x","y"＞" => OrdPair_mk x y
notation "＜"x","y"＞s" => OrdPair_is_Set x y

-- ordered triple
noncomputable def OrdTriple_mk (X Y Z: Class) [Set X] [Set Y] [Set Z] : Class :=
  @OrdPair_mk ＜X, Y＞ Z ＜X, Y＞s _
notation "＜"x","y","z"＞" => OrdTriple_mk x y z

-- 5. AxiomProduct
axiom AxiomProduct :
  ∀X Y: Class, ∃Z: Class,
    ∀z: Class, (z∈Z ↔ ∃x y: Class, ∃hx: x ∈ X,∃hy: y ∈ Y,
      (z ＝ (@OrdPair_mk x y (Set.mk₁ hx) (Set.mk₁ hy))))
noncomputable def ProductClass_mk (X Y: Class) : Class :=
  choose (AxiomProduct X Y)
noncomputable instance : HasProduct Class where
  Product := ProductClass_mk

-- Relation type
def isRelation (R : Class) : Prop :=
  ∀z: Class, z∈R ↔ ∃x y: Class, ∃_: Set x, ∃_: Set y,
    (z ＝ ＜x, y＞)
class Relation (R : Class) where
  isRelation: isRelation R

-- Function type
def isFunction (F : Class) [Relation F] : Prop :=
  ∀x x' y y': Class, ∀_: Set x, ∀_: Set x', ∀_: Set y, ∀_: Set y',
    ＜x, y＞ ∈ F → ＜x', y'＞ ∈ F → x ＝x' → y ＝ y'
class Function (F : Class) extends Relation F where
  isFunction : isFunction F

-- 6. AxiomInversion
axiom AxiomInversion :
  ∀X: Class, ∃Y: Class,
    ∀z: Class, (z ∈ Y)
      ↔ (∃x y: Class, ∃_: Set x, ∃_: Set y, ∃_:＜x,y＞ ∈ X,
        (z ＝ (＜y, x＞)))

theorem RelInvExists (R: Class):
  ∃RelInv_R: Class,
    ∀z: Class, (z ∈ RelInv_R)
      ↔ (∃x y: Class, ∃_: Set x, ∃_: Set y, ∃_:＜x,y＞ ∈ R,
        (z ＝ (＜y, x＞))) := AxiomInversion R
noncomputable def RelInv (R: Class): Class :=
  choose (AxiomInversion R)

-- 7. AxiomDomain
axiom AxiomDomain :
  ∀X: Class, ∃D: Class,
    ∀x: Class, ∀_: Set x,
      (x∈D ↔ ∃y: Class, ∃_: Set y, (＜x, y＞ ∈ X))

noncomputable def Dom (X: Class): Class :=
  choose (AxiomDomain X)
noncomputable def Rng (X: Class) [Relation X]: Class :=
  choose (AxiomDomain (RelInv X))

-- 8. AxiomMembership
axiom AxiomMembership :
  ∃E: Class,
    ∀x y: Class, ∀_: Set x, ∀_: Set y,
      (＜x, y＞ ∈ E ↔ x∈y)

-- class E
noncomputable def E: Class := choose AxiomMembership

-- Image type
theorem ImageClassExists (R X: Class) [hR: Relation R]:
  ∃Im: Class, ∀y: Class, ∀_: Set y,
    ((y ∈ Im)
      ↔ (∃x: Class, ∃(hx:x ∈ X), ((@OrdPair_mk x y (Set.mk₁ hx) _)∈ R))) := by {
  have : Relation (R ∩ (X ✕ U)) := sorry;
  let im := Rng (R ∩ (X ✕ U));
  exists im;
  sorry;
}
noncomputable def Im (R X: Class) [Relation R]: Class :=
  choose (ImageClassExists R X)

-- PowerClass
noncomputable def PowerClass_mk' (X : Class) : Class :=
  Diff U (Dom ((RelInv E) ∩ (U ✕ (Diff U X))))

theorem PowerClassExists (X : Class):
  ∃PX: Class,
    ∀z: Class, ∀_: Set z,
      z ∈ PX ↔ (z ⊂ X) := by {
  let px := Diff U (Dom ((RelInv E) ∩ (U ✕ (Diff U X))));
  exists px;
  sorry;
}

noncomputable def PowerClass_mk (X : Class) : Class :=
  choose (PowerClassExists X)
noncomputable instance : HasPow Class where
  Pow := PowerClass_mk

-- 9. AxiomCycle
axiom AxiomCycle :
  ∀X: Class, ∃Y: Class, ∀u v w: Class,
    ∃_: Set u, ∃_: Set v, ∃_: Set w,
      ＜u,v,w＞ ∈ X ↔ ＜w,u,v＞ ∈ Y
-- 10. AxiomReplacement
axiom AxiomReplacement :
  ∀F x: Class, ∀(hF: Function F), ∀(_: Set x),
    isSet (@Im F x hF.1)

-- 11. AxiomUnion
axiom AxiomUnion:
  ∀x: Class, (Set x) → ∃Z: Class,
    (Z ∈ U) ∧ (∀z: Class, z∈Z ↔ (∃y: Class, y∈x → z∈y))

noncomputable def UnionSet_mk (x: Class) [hx: Set x]: Class :=
  choose (AxiomUnion x hx)
-- 12. AxiomPowerSet
axiom AxiomPowerSet :
  ∀x: Class, Set x → isSet (𝒫 x)
-- 13. AxiomInfinity
axiom AxiomInfinity :
  ∃x: Class, (x∈U)
    ∧ ((ø∈x) ∧ ∀n: Class,
      ((hn: n ∈ x) → (n ∪ (@Singleton_mk n (Set.mk₁ hn))) ∈ x))

-- 14. AxiomFoundation
axiom AxiomFoundation :
  ∀x: Class, Set x
    → ¬ x＝ø → (∃y: Class, y∈x ∧ (∀z: Class, z∈y → z∉x))

-- 15. AxiomGlobalChoice
axiom AxiomGlobalChoice:
  ∃F: Class,∃_: Function F,∀x: Class, ∀_: Set x,
    (¬ x＝ø → (∃y: Class,∃hy: y∈x,
      (@Pair_mk x y _ (Set.mk₁ hy)) ∈ F))