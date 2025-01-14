import FMCn.IRI.Nat.Definitions

namespace data

inductive BinTree (α : Type) where
  | Leaf : α → BinTree α
  | Fork : BinTree α → BinTree α → BinTree α

def nodes : BinTree α → Nat
  | .Leaf _ => .O
  | .Fork l r => .S (nodes l + nodes r)

def tips : BinTree α → Nat
  | .Leaf _ => .S .O
  | .Fork l r => tips l + tips r

