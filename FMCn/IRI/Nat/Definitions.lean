import FMCn.CFR1.Functions
import FMCn.IRI.Bool.Definitions
namespace data

inductive Nat where
  | O : Nat
  | S : Nat → Nat

def fromNat : Nat → String
  | .O => "O"
  | .S n => "S" ++ fromNat n

instance : Repr Nat where
  reprPrec
  | n, _ => Std.Format.text (fromNat n)

def eq : Nat → Nat → Bool
  | .O, .O => .true
  | .S n, .S m => eq n m
  | _, _ => .false
infix:65 " == " => eq

def pred : Nat → Nat
  | .O => .O
  | .S n => n

#eval pred (.S (.S .O))

def monus : Nat → Nat → Nat
  | .S n, .S m => monus n m
  | n, _ => n
infix:65 " ∸ " => monus

def add : Nat → Nat → Nat
  | n, .O => n
  | n, .S m => .S (add n m)
infixl:65 " + " => add

def mul : Nat → Nat → Nat
  | _, .O => .O
  | n, .S m => mul n m + n
infixl:70 " * " => mul

def pow : Nat → Nat → Nat
  | _, .O => .S .O
  | n, .S m => pow n m * n
infixr:75 " ^ " => pow

def leq : Nat → Nat → Bool
  | .O, _ => .true
  | _, .O => .false
  | .S n, .S m => leq n m
infix:65 " ≤ " => leq

def lt : Nat → Nat → Bool
  | _, .O => .false
  | .O, _ => .true
  | .S n, .S m => lt n m
infix:65 " < " => lt

def double : Nat → Nat
  := uncurry add ⋄ Δ

def fact : Nat → Nat
  | .O => (.S .O)
  | .S n => mul (.S n) (fact n)

def fib : Nat → Nat
  | .S (.S n) => fib (.S n) + fib n
  | n => n

def min₂ : Nat → Nat → Nat
  | .S n, .S m => .S (min₂ n m)
  | _, _ => .O

def max₂ : Nat → Nat → Nat
  | .O, m => m
  | n, .O => n
  | .S n, .S m => .S (max₂ n m)

def mod : Nat → Nat → Nat
  | n, m => if n ≤ m
            then m ∸ n
            else n ∸ m

def mod' : Nat → Nat → Nat
  | .O, m => m
  | n, .O => n
  | .S n, .S m => mod' n m
notation:70 "∣" n " − " m "∣" => mod n m

open Nat

#eval mod O (S (S O)) + O

/-
def div : Nat × Nat → 𝟙 ⊕ Nat × Nat
  | ⟨_, .O⟩ => .inl ()
  | ⟨n, m⟩ => if n < m then .inr ⟨.O, n⟩ else div ⟨.S (n ∸ m), m⟩

def quot : Nat × Nat → 𝟙 ⊕ Nat
  := sorry
-/
mutual
def even : Nat → Bool
  | .O => .true
  | .S n => odd n

def odd : Nat → Bool
  | .O => .false
  | .S n => even n
end

def Zero : Nat → Bool
  | .O => .true
  | _ => .false

def stripMaybe : Nat ⊕ 𝟙 → Nat
  | .inl n => n
  | .inr () => .O

def geq (a b : Nat) : Prop := ∃ (x : Nat), b + x = a
infix:90 " ≥ " => geq
