import FMCn.CFR1.Functions
namespace data

inductive Nat where
  | O : Nat
  | S : Nat → Nat
deriving Repr

def eq : Nat → Nat → Bool
  | .O, .O => .true
  | .S n, .S m => eq n m
  | _, _ => .false
infix:65 " == " => eq

def pred : Nat → Nat
  | .O => .O
  | .S n => n

def add : Nat → Nat → Nat
  | n, .O => n
  | n, .S m => .S (add n m)
infixl:65 " + " => add

def mul : Nat → Nat → Nat
  | _, .O => .O
  | n, .S m => mul n m + n
infixl:65 " * " => mul

def pow : Nat → Nat → Nat
  | _, .O => .S .O
  | n, .S m => pow n m * n
infixr:65 " ^ " => pow

def leq : Nat → Nat → Bool
  | .O, _ => true
  | _, .O => false
  | .S n, .S m => leq n m
infix:65 " ≤ " => leq

def lt : Nat → Nat → Bool
  | _, .O => false
  | .O, _ => true
  | .S n, .S m => lt n m
infix:65 " < " => lt

def double : Nat → Nat
  := uncurry add ⋄ Δ

def min₂ : Nat → Nat → Nat
  | .S n, .S m => .S (min₂ n m)
  | _, _ => .O

def max₂ : Nat → Nat → Nat
  | .O, m => m
  | n, .O => n
  | .S n, .S m => .S (max₂ n m)

mutual
def even : Nat → Bool
  | .O => true
  | .S n => odd n

def odd : Nat → Bool
  | .O => false
  | .S n => even n
end

def Zero : Nat → Bool
  | .O => true
  | _ => false

def stripMaybe : Nat ⊕ Unit → Nat
  | .inl n => n
  | .inr () => .O

axiom peano_neg {n : Nat} : ¬ Nat.O = Nat.S n
