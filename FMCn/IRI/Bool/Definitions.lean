import FMCn.CFR1.Functions

namespace data

inductive Bool where
  | true : Bool
  | false : Bool

def Bool.fromBool : Bool → String
  | .true => "true"
  | .false => "false"

instance : Repr Bool where
  reprPrec
    | b, _ => Std.Format.text (Bool.fromBool b)

def Bool.band : Bool → Bool → Bool
  | .true, .true => .true
  | _, _ => .false
infixl:60 " and " => Bool.band

def Bool.bor : Bool → Bool → Bool
  | .false, .false => .false
  | _, _ => .true
infixl:55 " or " => Bool.bor

def Bool.bxor : Bool → Bool → Bool
  | .true, .false => .true
  | .false, .true => .true
  | _, _ => .false
infixl:60 " xor " => Bool.bxor

def Bool.not : Bool → Bool
  | .true => .false
  | _ => .true

def Bool.bnand : Bool → Bool → Bool
  := curry (not ⋄ uncurry band)
infixl:60 " nand " => Bool.bnand

def Bool.bnor : Bool → Bool → Bool
  := curry (not ⋄ uncurry bor)
infixl:60 " nor " => Bool.bnor

def bxnor : Bool → Bool → Bool
  := curry (Bool.not ⋄ uncurry Bool.bxor)
infixl:60 " xnor " => bxnor

def Bool.if_then_else : Bool → α → α → α
  | .true, a, _ => a
  | .false, _, a => a
notation:max "if " b " then " x " else " y => Bool.if_then_else b x y
