namespace data

inductive Maybe (α : Type) where
  | Nothing : Maybe α
  | Just : α → Maybe α

def Mmap : (α → β) → Maybe α → Maybe β
  | _, .Nothing => .Nothing
  | f, .Just a => .Just (f a)

def bind : Maybe α → (α → Maybe β) → Maybe β
  | .Nothing, _ => .Nothing
  | .Just x, f => f x
infix:50 ">>= " => bind
