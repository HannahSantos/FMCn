import FMCn.IEA.Magma.Definition

class Semigroup (α : Type u) extends Magma α where
  Op_Ass : ∀ (a b c : α), a ⋆ b ⋆ c = a ⋆ (b ⋆ c)
