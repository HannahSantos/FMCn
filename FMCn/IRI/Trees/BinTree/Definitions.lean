import FMCn.IRI.Nat.Definitions

namespace data

inductive BinTree (α : Type) where
  | Leaf : α → BinTree α
  | Fork : BinTree α → BinTree α → BinTree α

def BTmap : (α → β) → BinTree α → BinTree β
  | f, .Leaf x => .Leaf (f x)
  | f, .Fork l r => .Fork (BTmap f l) (BTmap f r)

def nodes : BinTree α → Nat
  | .Leaf _ => .O
  | .Fork l r => .S (nodes l + nodes r)

def tips : BinTree α → Nat
  | .Leaf _ => .S .O
  | .Fork l r => tips l + tips r

def depth : BinTree α → Nat
  | .Leaf _ => .O
  | .Fork l r => .S (max₂ (depth l) (depth r))

