import FMCn.CFR1.Functions

namespace data

inductive Bool where
  | true : Bool
  | false : Bool

def fromBool : Bool → String
  | .true => "true"
  | .false => "false"

instance : Repr Bool where
  reprPrec
    | b, _ => Std.Format.text (fromBool b)

def band : Bool → Bool → Bool
  | .true, .true => .true
  | _, _ => .false
infixl:60 " and " => band

def bor : Bool → Bool → Bool
  | .false, .false => .false
  | _, _ => .true
infixl:55 " or " => bor

def bxor : Bool → Bool → Bool
  | .true, .false => .true
  | .false, .true => .true
  | _, _ => .false
infixl:60 " xor " => bxor

def not : Bool → Bool
  | .true => .false
  | _ => .true

def bnand : Bool → Bool → Bool
  := curry (not ⋄ uncurry band)
infixl:60 " nand " => bnand

def bnor : Bool → Bool → Bool
  := curry (not ⋄ uncurry bor)
infixl:60 " nor " => bnor

def bxnor : Bool → Bool → Bool
  := curry (not ⋄ uncurry bxor)
infixl:60 " xnor " => bxnor

def if_then_else : Bool → α → α → α
  | .true, a, _ => a
  | .false, _, a => a
notation:max "if " b " then " x " else " y => if_then_else b x y
