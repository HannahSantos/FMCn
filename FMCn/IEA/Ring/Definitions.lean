import FMCn.IEA.Group.Definitions

class Ring (R : Type) extends GroupA R, MonoidM R where
  distrR : ∀ (a b c : R), c ⋆ (a ⊹ b) = c ⋆ a ⊹ c ⋆ b
  distrL : ∀ (a b c : R), (a ⊹ b) ⋆ c = a ⋆ c ⊹ b ⋆ c
