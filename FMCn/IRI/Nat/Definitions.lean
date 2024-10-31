namespace data

inductive Nat where
  | O : Nat
  | S : Nat → Nat
deriving Repr

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

axiom peano_neg {n : Nat} : ¬ Nat.O = Nat.S n
