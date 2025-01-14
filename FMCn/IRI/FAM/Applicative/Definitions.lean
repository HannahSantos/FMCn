import FMCn.CFR1.Functions
import FMCn.IRI.FAM.Functor.Definitions

namespace data

class Applicative (f : Type → Type) extends Functor f where
  pure : α → f α
  splat : f (α → β) → f α → f β
  Pure_Id_law (v : f α) : splat (pure id) v = v
  Homo_law (f : α → β) (x : α) : splat (pure f) (pure x) = pure (f x)
  law (u : f (α → β)) (x : α) : splat u (pure x) = sorry
  law2 (u : f (β → γ)) (v : f (α → β)) (w : f α) : splat u (splat v w) = sorry
infix:50 " ⊛ " => Applicative.splat

