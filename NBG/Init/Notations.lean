
universe u
variable (α : Type u)

class HasEq  (α : Type u) where
  Eq : α → α → Prop
infix:50 " ＝ "  => HasEq.Eq

class HasMem  (α : Type u) where
  Mem : α → α → Prop
infix:50 " ∈ "  => HasMem.Mem

class HasSubset  (α : Type u) where
  Subset : α → α → Prop
infix:50 " ⊂ "  => HasSubset.Subset
infix:50 " ⊆ "  => HasSubset.Subset

class HasUnion  (α : Type u) where
  Union : α → α → α
infix:50 " ∪ "  => HasUnion.Union

class HasInter  (α : Type u) where
  Inter : α → α → α
infix:50 " ∩ "  => HasInter.Inter

class HasUnionAll  (α : Type u) where
  UnionAll : α → α
infix:50 " ⋃ "  => HasUnionAll.UnionAll

class HasInterAll  (α : Type u) where
  InterAll : α → α
infix:50 " ⋂ "  => HasInterAll.InterAll

class HasPow  (α : Sort u) where
  Pow : α → α
notation "𝒫" => HasPow.Pow

class HasDiff  (α : Type u) where
  Diff : α → α → α
infix:50 " ＼ "  => HasDiff.Diff



