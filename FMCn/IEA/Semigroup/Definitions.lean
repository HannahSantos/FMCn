import FMCn.IEA.Magma.Definition

class SemigroupM (α : Type u) extends MagmaM α where
  opm_ass : ∀ (a b c : α), (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c)

class SemigroupA (α : Type u) extends MagmaA α where
  opa_ass : ∀ (a b c : α), (a ⊹ b) ⊹ c = a ⊹ (b ⊹ c)
