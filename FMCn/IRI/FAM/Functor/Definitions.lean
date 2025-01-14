import FMCn.CFR1.Functions

namespace data

class Functor (f : Type → Type) where
  fmap : (α → β) → f α → f β
  Id_law {α : Type} : ∀ (t : f α), (fmap id) t = id t
  Comp_law {g : β → γ} {h : α → β}: fmap (g ⋄ h) = fmap g ⋄ fmap h

