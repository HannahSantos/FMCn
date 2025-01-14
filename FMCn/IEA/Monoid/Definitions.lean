import FMCn.IEA.Semigroup.Definitions

class Monoid (α : Type u) extends Semigroup α where
  e : α
  Id_Op : ∀ (a : α), e ⋆ a = a
  Op_Id : ∀ (a : α), a ⋆ e = a
open Monoid

def idM [Monoid M] (x : M) : Prop :=
  (∀ (a : M), a ⋆ x = a) ∧ ∀ (b : M), x ⋆ b = b
notation:65 x:65 " é a identidade" => idM x

------------------------------------------------
-- Pows :
------------------------------------------------

def Pow_R [Monoid M] : M → Nat → M
  | _, 0 => e
  | a, .succ n => a ⋆ (Pow_R a n)
notation:65 lhs:65 " ↑ᴿ " rhs:66 => Pow_R lhs rhs

def Pow_L [Monoid M] : Nat → M → M
  | 0, _ => e
  | .succ n, a => (Pow_L n a) ⋆ a
notation:65 lhs:65 " ↑ᴸ " rhs:66 => Pow_L rhs lhs
