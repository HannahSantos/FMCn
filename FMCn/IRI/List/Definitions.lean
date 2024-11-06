import FMCn.IRI.Nat.Definitions

namespace data

inductive List (α : Type) where
  | Nil : List α
  | Cons : α → List α → List α
  deriving Repr

infixr:70 "∷" => List.Cons
notation:70 "‖" α "‖" => List α
notation:75 "⟦⟧" => List.Nil

open List Nat

def fmap : (α → β) → ‖α‖ → ‖β‖
  | _, ⟦⟧ => ⟦⟧
  | f, x∷xs => f x∷fmap f xs

def length : ‖α‖ → Nat
  | ⟦⟧ => O
  | _∷xs => S (length xs)

def elem : Nat → ‖Nat‖ → Bool
  | _, ⟦⟧ => false
  | n, x∷xs => n == x || elem n xs

def FoldL : (α → β → β) → β → ‖α‖ → β
  | _, e, ⟦⟧ => e
  | op, e, x∷xs => op x (FoldL op e xs)

def sum : ‖Nat‖ → Nat
  := FoldL (λx : Nat => λy => x + y) O

def product : ‖Nat‖ → Nat
  := FoldL (λx : Nat => λy => x + y) (S O)

def concat : ‖α‖ → ‖α‖ → ‖α‖
  | ⟦⟧, ys => ys
  | x∷xs, ys => x∷concat xs ys
infixl:65 " ++ " => concat

def append : α → ‖α‖ → ‖α‖
  | n, ⟦⟧ => n∷⟦⟧
  | n, x∷xs => x∷append n xs

def append_cat : α → ‖α‖ → ‖α‖
  | n, xs => xs ++ n∷⟦⟧

-- esreveR...
def reverse : ‖α‖ → ‖α‖
  | ⟦⟧ => ⟦⟧
  | x∷xs => append x (reverse xs)

def rev : ‖α‖ → ‖α‖
  | ⟦⟧ => ⟦⟧
  | x∷xs => rev xs ++ x∷⟦⟧

def revcat : ‖α‖ → ‖α‖ → ‖α‖
  | ⟦⟧, ys => ys
  | x∷xs, ys => revcat xs (x∷ys)

def filter : (α → Bool) → ‖α‖ → ‖α‖
  | _, ⟦⟧ => ⟦⟧
  | p, x∷xs => let xs' := filter p xs
               if p x then x∷xs' else xs'

def All : (α → Bool) → ‖α‖ → Bool
  | _, ⟦⟧ => true
  | p, x∷xs => p x && All p xs

def Any : (α → Bool) → ‖α‖ → Bool
  | _, ⟦⟧ => false
  | p, x∷xs => p x || Any p xs

def doubleList : ‖Nat‖ → ‖Nat‖
  := fmap double

def addNat : Nat → ‖Nat‖ → ‖Nat‖
  := λn => fmap (λx : Nat => x + n)

def multNat : Nat → ‖Nat‖ → ‖Nat‖
  := λn => fmap (λx : Nat => x * n)

def expNat : Nat → ‖Nat‖ → ‖Nat‖
  := λn => fmap (λx : Nat => x ^ n)

def enumTo : Nat → ‖Nat‖
  | S n => append (S n) (enumTo n)
  | _ => O∷⟦⟧

def replicate : Nat → α → ‖α‖
  | O, _ => ⟦⟧
  | S n, a => a∷replicate n a

def take : Nat → ‖α‖ → ‖α‖
  | S n, x∷xs => x∷take n xs
  | _, _ => ⟦⟧

def takeWhile : (α → Bool) → ‖α‖ → ‖α‖
  | _, ⟦⟧ => ⟦⟧
  | p, x∷xs => let xs' := takeWhile p xs
               if p x then x∷xs' else ⟦⟧

def drop : Nat → ‖α‖ → ‖α‖
  | S n, _∷xs => drop n xs
  | _, xs => xs

def dropWhile : (α → Bool) → ‖α‖ → ‖α‖
  | _, ⟦⟧ => ⟦⟧
  | p, x∷xs => if p x then dropWhile p xs else x∷xs

def elemIndices : Nat → ‖Nat‖ → ‖Nat‖
  | n, x∷xs => let xs' := elemIndices n xs
               if n == x then O∷addNat (S O) xs'
               else addNat (S O) xs'
  | _, ⟦⟧ => ⟦⟧

def pw : (α → β → γ) → ‖α‖ → ‖β‖ → ‖γ‖
  | op, x∷xs, y∷ys => (op x y)∷(pw op xs ys)
  | _, _, _ => ⟦⟧

def pwAdd : ‖Nat‖ → ‖Nat‖ → ‖Nat‖
  := pw (λx => λy => x + y)

def pwMult : ‖Nat‖ → ‖Nat‖ → ‖Nat‖
  := pw (λx => λy => x * y)

def isSorted : ‖Nat‖ → Bool
  | x∷xs@(x'∷_) => x ≤ x' && isSorted xs
  | _ => true

def minimum : ‖Nat‖ → Nat ⊕ Unit
  | n∷⟦⟧ => .inl n
  | n∷ns => .inl (min₂ n (stripMaybe (minimum ns)))
  | _ => .inr ()

def maximum : ‖Nat‖ → Nat
  | ⟦⟧ => O
  | x∷xs => max₂ x (maximum xs)

def isPrefixOf : ‖Nat‖ → ‖Nat‖ → Bool
  | ⟦⟧, _ => true
  | x∷xs, y∷ys => x == y && isPrefixOf xs ys
  | _, _ => false

def mix : ‖α‖ → ‖α‖ → ‖α‖
  | x∷xs, y∷ys => x∷(y∷(mix xs ys))
  | _, _ => ⟦⟧

def interspace : α → ‖α‖ → ‖α‖
  | _, ys@(_∷⟦⟧) => ys
  | x, y∷ys => y∷x∷interspace x ys
  | _, ⟦⟧ => ⟦⟧

-- Assume ordered lists
-- First element greater than n
def upper_bound : Nat → ‖Nat‖ → Nat
  | _, ⟦⟧ => O
  | n, x∷xs => if n < x then x else upper_bound n xs

-- Assume ordered lists
-- First element not less than n
def lower_bound : Nat → ‖Nat‖ → Nat
  | _, ⟦⟧ => .O
  | n, x∷xs => if n ≤ x then x else lower_bound n xs
