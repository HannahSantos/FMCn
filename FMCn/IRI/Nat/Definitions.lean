import FMCn.CFR1.Functions
import FMCn.IRI.Bool.Definitions
namespace data

inductive Nat where
  | O : Nat
  | S : Nat → Nat

def Nat.fromNat : Nat → String
  | .O => "O"
  | .S n => "S" ++ (fromNat n)

instance : Repr Nat where
  reprPrec
  | n, _ => Std.Format.text (Nat.fromNat n)

def Nat.eq : Nat → Nat → Bool
  | .O, .O => .true
  | .S n, .S m => eq n m
  | _, _ => .false
infix:65 " == " => Nat.eq

def Nat.pred : Nat → Nat
  | .O => .O
  | .S n => n

#eval Nat.pred (.S (.S .O))

def Nat.monus : Nat → Nat → Nat
  | .S n, .S m => monus n m
  | n, _ => n
infix:65 " ∸ " => Nat.monus

def Nat.add : Nat → Nat → Nat
  | n, .O => n
  | n, .S m => .S (add n m)
infixl:65 " + " => Nat.add

def Nat.mul : Nat → Nat → Nat
  | _, .O => .O
  | n, .S m => mul n m + n
infixl:70 " * " => Nat.mul

def Nat.pow : Nat → Nat → Nat
  | _, .O => .S .O
  | n, .S m => pow n m * n
infixr:75 " ^ " => Nat.pow

def Nat.leq : Nat → Nat → Bool
  | .O, _ => .true
  | _, .O => .false
  | .S n, .S m => leq n m
infix:65 " ≤ " => Nat.leq

def Nat.lt : Nat → Nat → Bool
  | _, .O => .false
  | .O, _ => .true
  | .S n, .S m => lt n m
infix:65 " < " => Nat.lt

def Nat.double : Nat → Nat
  := uncurry add ⋄ Δ

def Nat.fact : Nat → Nat
  | .O => (.S .O)
  | .S n => mul (.S n) (fact n)

def Nat.fib : Nat → Nat
  | .S (.S n) => fib (.S n) + fib n
  | n => n

def Nat.min₂ : Nat → Nat → Nat
  | .S n, .S m => .S (min₂ n m)
  | _, _ => .O

def Nat.max₂ : Nat → Nat → Nat
  | .O, m => m
  | n, .O => n
  | .S n, .S m => .S (max₂ n m)

def Nat.mod : Nat → Nat → Nat
  | n, m => if n ≤ m
            then m ∸ n
            else n ∸ m

def Nat.mod' : Nat → Nat → Nat
  | .O, m => m
  | n, .O => n
  | .S n, .S m => mod' n m
notation:70 "∣" n " − " m "∣" => Nat.mod n m

open Nat

#eval mod O (S (S O)) + O

/-
def Nat.div : Nat × Nat → 𝟙 ⊕ Nat × Nat
  | ⟨_, .O⟩ => .inl ()
  | ⟨n, m⟩ => if n < m then .inr ⟨.O, n⟩ else div ⟨.S (n ∸ m), m⟩

def Nat.quot : Nat × Nat → 𝟙 ⊕ Nat
  := sorry
-/
mutual
def Nat.even : Nat → Bool
  | .O => .true
  | .S n => odd n

def Nat.odd : Nat → Bool
  | .O => .false
  | .S n => even n
end

def Nat.Zero : Nat → Bool
  | .O => .true
  | _ => .false

def Nat.stripMaybe : Nat ⊕ 𝟙 → Nat
  | .inl n => n
  | .inr () => .O

def Nat.geq (a b : Nat) : Prop := ∃ (x : Nat), b + x = a
infix:90 " ≥ " => Nat.geq
