import FMCn.CFR1.Functions
import FMCn.IRI.FAM.Functor.Definitions
import FMCn.IRI.FAM.Applicative.Definitions

namespace data

class Monad (m : Type → Type) extends Applicative m where
  join : m (m α) → m α
  bind : m α → (α → m β) → m β
  kleisli_comp : (α → m β) → (β → m γ) → (α → m γ)

open Monad Applicative Functor

def bind' [Monad m]: m α → (α → m β) → m β
  | ax, f => join (pure f ⊛ ax)
infix:75 " >>= " => Monad.bind

def bind'' [Monad m] : m α → (α → m β) → m β
  | ax, f => join (fmap f ax)

def join' [Monad m] : m (m α) → m α
  | axx => axx >>= id

def fmap' [Monad m] : (α → β) → m α → m β
  | f, ax => ax >>= (pure ⋄ f)

def kleisli_comp' [Monad m] : (α → m β) → (β → m γ) → (α → m γ)
  | f, g, a => f a >>= g
infix:75 " >=> " => Monad.kleisli_comp
