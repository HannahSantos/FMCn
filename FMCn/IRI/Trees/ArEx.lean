inductive ArEx where
  | Plus : ArEx → ArEx → ArEx
  | Times : ArEx → ArEx → ArEx
  | Neg : ArEx → ArEx
  | Atom : Int → ArEx

def eval : ArEx → Int
  | .Plus s t => eval s + eval t
  | .Times s t => eval s * eval t
  | .Neg s => -(eval s)
  | .Atom s => s

def height : ArEx → Nat
  | .Plus s t => max (height s) (height t)
  | .Times s t => max (height s) (height t)
  | .Neg s => .succ (height s)
  | .Atom _ => 0
