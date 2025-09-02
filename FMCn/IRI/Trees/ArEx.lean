import FMCn.IRI.Nat.Definitions
import FMCn.IRI.Nat.Theorems

namespace data

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
  | .Plus s t => Nat.max₂ (height s) (height t)
  | .Times s t => Nat.max₂ (height s) (height t)
  | .Neg s => .S (height s)
  | .Atom _ => .O
