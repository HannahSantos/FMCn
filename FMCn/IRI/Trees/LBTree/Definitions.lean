import FMCn.IRI.List.Definitions

namespace data

inductive LBTree (α β : Type) where
  | Tip : α → LBTree α β
  | Fork : β → LBTree α β → LBTree α β → LBTree α β

def flatten' : LBTree α β → ‖α ⊕ β‖ → ‖α ⊕ β‖
  | .Tip a, xs => .inl a∷xs
  | .Fork b l r, xs => flatten' l (.inr b∷flatten' r xs)

def flatten : LBTree α β → ‖α ⊕ β‖
  | .Tip a => ⟦.inl a⟧
  | .Fork b l r => flatten l ++ .inr b∷flatten r

def mirror : LBTree α β → LBTree α β
  | .Tip a => .Tip a
  | .Fork b l r => .Fork b (mirror r) (mirror l)
