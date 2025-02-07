import FMCn.IRI.Nat.Definitions
import FMCn.IRI.Bool.Definitions
import FMCn.IRI.Maybe.Definitions

namespace data

inductive List (α : Type) where
  | Nil : List α
  | Cons : α → List α → List α
  deriving Repr

infixr:70 "∷" => List.Cons
notation:max "‖" α "‖" => List α
notation:75 "⟦⟧" => List.Nil
notation:80 "⟦" x "⟧" => x∷⟦⟧

open List Nat

-----------------------Destructors---------------------

def safehead : ‖α‖ → Maybe α
  | x∷_ => .Just x
  | _ => .Nothing

def safetail : ‖α‖ → Maybe ‖α‖
  | ⟦⟧ => .Nothing
  | _∷xs => .Just xs

def stripMaybeL : Maybe ‖α‖ → ‖α‖
  | .Just xs => xs
  | .Nothing => ⟦⟧

-------------------------------------------------------

def Lmap : (α → β) → ‖α‖ → ‖β‖
  | _, ⟦⟧ => ⟦⟧
  | f, x∷xs => f x∷Lmap f xs

def length : ‖α‖ → Nat
  | ⟦⟧ => O
  | _∷xs => S (length xs)

def elem : Nat → ‖Nat‖ → Bool
  | _, ⟦⟧ => .false
  | n, x∷xs => (n == x) or elem n xs

def FoldR : (α → β → β) → β → ‖α‖ → β
  | _, e, ⟦⟧ => e
  | ρ, e, x∷xs => ρ x (FoldR ρ e xs)

def zip : ‖α‖ → ‖β‖ → ‖α × β‖
  | x∷xs, y∷ys => ⟨x, y⟩∷zip xs ys
  | _, _ => ⟦⟧

def zipWith : (α → β → γ) → ‖α‖ → ‖β‖ → ‖γ‖
  | op, x∷xs, y∷ys => op x y∷zipWith op xs ys
  | _, _, _ => ⟦⟧

def Lsplat' : ‖α → β‖ → ‖α‖ → ‖β‖
  := zipWith (λ f x => f $ x)

def cp : ‖α‖ → ‖β‖ → ‖α × β‖
  | f∷fs, xs => sorry
  | ⟦⟧, _ => ⟦⟧

def Lsplat : ‖α → β‖ → ‖α‖ → ‖β‖
  := sorry

def sum : ‖Nat‖ → Nat
  := FoldR (λ (x y : Nat) => x + y) O

def product : ‖Nat‖ → Nat
  := FoldR (λ (x y : Nat) => x * y) (S O)

def concat : ‖α‖ → ‖α‖ → ‖α‖
  | ⟦⟧, ys => ys
  | x∷xs, ys => x∷concat xs ys
infixl:65 " ++ " => concat

def append : α → ‖α‖ → ‖α‖
  | n, ⟦⟧ => n∷⟦⟧
  | n, x∷xs => x∷append n xs

def append_cat : α → ‖α‖ → ‖α‖
  | n, xs => xs ++ ⟦n⟧

-- esreveR...
def reverse : ‖α‖ → ‖α‖
  | ⟦⟧ => ⟦⟧
  | x∷xs => append x (reverse xs)

def rev : ‖α‖ → ‖α‖
  | ⟦⟧ => ⟦⟧
  | x∷xs => rev xs ++ ⟦x⟧

def revcat : ‖α‖ → ‖α‖ → ‖α‖
  | ⟦⟧, ys => ys
  | x∷xs, ys => revcat xs (x∷ys)

def filter : (α → Bool) → ‖α‖ → ‖α‖
  | _, ⟦⟧ => ⟦⟧
  | p, x∷xs => let xs' := filter p xs
               if p x then x∷xs' else xs'

def All : (α → Bool) → ‖α‖ → Bool
  | _, ⟦⟧ => .true
  | p, x∷xs => p x and All p xs

def Any : (α → Bool) → ‖α‖ → Bool
  | _, ⟦⟧ => .false
  | p, x∷xs => p x or Any p xs

def doubleList : ‖Nat‖ → ‖Nat‖
  := Lmap double

def addNat : Nat → ‖Nat‖ → ‖Nat‖
  | n => Lmap (λx : Nat => x + n)

def multNat : Nat → ‖Nat‖ → ‖Nat‖
  | n => Lmap (λx : Nat => x * n)

def expNat : Nat → ‖Nat‖ → ‖Nat‖
  | n => Lmap (λx : Nat => x ^ n)

def enumTo : Nat → ‖Nat‖
  | S n => append (S n) (enumTo n)
  | _ => ⟦O⟧

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
  | p, xs@(x'∷xs') => if p x' then dropWhile p xs' else xs

def elemIndices : Nat → ‖Nat‖ → ‖Nat‖
  | n, x∷xs => let xs' := elemIndices n xs
               if n == x then O∷addNat (S O) xs'
               else addNat (S O) xs'
  | _, _ => ⟦⟧

def pw : (α → β → γ) → ‖α‖ → ‖β‖ → ‖γ‖
  | op, x∷xs, y∷ys => (op x y)∷(pw op xs ys)
  | _, _, _ => ⟦⟧

def pwAdd : ‖Nat‖ → ‖Nat‖ → ‖Nat‖
  := pw (λx => λy => x + y)

def pwMult : ‖Nat‖ → ‖Nat‖ → ‖Nat‖
  := pw (λx => λy => x * y)

def isSorted : ‖Nat‖ → Bool
  | x∷xs@(x'∷_) => (x ≤ x') and isSorted xs
  | _ => .true

def minimum : ‖Nat‖ → Nat ⊕ Unit
  | n∷⟦⟧ => .inl n
  | n∷ns => .inl (min₂ n (stripMaybe (minimum ns)))
  | _ => .inr ()

def maximum : ‖Nat‖ → Nat
  | ⟦⟧ => O
  | x∷xs => max₂ x (maximum xs)

def isPrefixOf : ‖Nat‖ → ‖Nat‖ → Bool
  | ⟦⟧, _ => .true
  | x∷xs, y∷ys => (x == y) and isPrefixOf xs ys
  | _, _ => .false

def mix : ‖α‖ → ‖α‖ → ‖α‖
  | x∷xs, y∷ys => x∷y∷mix xs ys
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
