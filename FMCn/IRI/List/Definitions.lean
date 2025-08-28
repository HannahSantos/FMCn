import FMCn.IRI.Nat.Definitions
import FMCn.IRI.Bool.Definitions
import FMCn.IRI.Maybe.Definitions

namespace data

inductive List (α : Type) where
  | Nil : List α
  | Cons : α → List α → List α
  deriving Repr

infixr:70 "∷" => List.Cons
notation:max "⟦" α "⟧" => List α
notation:75 "⟦⟧" => List.Nil
notation:80 "⟦" x "⟧" => x∷⟦⟧

-----------------------Destructors---------------------

def List.safehead : ⟦α⟧ → Maybe α
  | x∷_ => .Just x
  | _ => .Nothing

def List.safetail : ⟦α⟧ → Maybe ⟦α⟧
  | ⟦⟧ => .Nothing
  | _∷xs => .Just xs

def List.stripMaybeL : Maybe ⟦α⟧ → ⟦α⟧
  | .Just xs => xs
  | .Nothing => ⟦⟧

-------------------------------------------------------

def List.Lmap : (α → β) → ⟦α⟧ → ⟦β⟧
  | _, ⟦⟧ => ⟦⟧
  | f, x∷xs => f x∷Lmap f xs

def List.length : ⟦α⟧ → Nat
  | ⟦⟧ => .O
  | _∷xs => .S (length xs)

def List.elem : Nat → ⟦Nat⟧ → Bool
  | _, ⟦⟧ => .false
  | n, x∷xs => (n == x) or elem n xs

def List.FoldR : (α → β → β) → β → ⟦α⟧ → β
  | _, e, ⟦⟧ => e
  | ρ, e, x∷xs => ρ x (FoldR ρ e xs)

def List.zip : ⟦α⟧ → ⟦β⟧ → ⟦α × β⟧
  | x∷xs, y∷ys => ⟨x, y⟩∷zip xs ys
  | _, _ => ⟦⟧

def List.zipWith : (α → β → γ) → ⟦α⟧ → ⟦β⟧ → ⟦γ⟧
  | op, x∷xs, y∷ys => op x y∷zipWith op xs ys
  | _, _, _ => ⟦⟧

def List.Lsplat' : ⟦α → β⟧ → ⟦α⟧ → ⟦β⟧
  := zipWith (λ f x => f $ x)
/-
def List.cp : ⟦α⟧ → ⟦β⟧ → ‖α × β‖
  | f∷fs, xs => sorry
  | ⟦⟧, _ => ⟦⟧

def List.Lsplat : ‖α → β‖ → ⟦α⟧ → ⟦β⟧
  := sorry
-/
def List.sum : ⟦Nat⟧ → Nat
  := FoldR (λ (x y : Nat) => x + y) .O

def List.product : ⟦Nat⟧ → Nat
  := FoldR (λ (x y : Nat) => x * y) (.S .O)

def List.concat : ⟦α⟧ → ⟦α⟧ → ⟦α⟧
  | ⟦⟧, ys => ys
  | x∷xs, ys => x∷concat xs ys
infixl:65 " ++ " => List.concat

def List.append : α → ⟦α⟧ → ⟦α⟧
  | n, ⟦⟧ => n∷⟦⟧
  | n, x∷xs => x∷append n xs

def List.append_cat : α → ⟦α⟧ → ⟦α⟧
  | n, xs => xs ++ ⟦n⟧

-- esreveR...
def List.reverse : ⟦α⟧ → ⟦α⟧
  | ⟦⟧ => ⟦⟧
  | x∷xs => append x (reverse xs)

def List.rev : ⟦α⟧ → ⟦α⟧
  | ⟦⟧ => ⟦⟧
  | x∷xs => rev xs ++ ⟦x⟧

def List.revcat : ⟦α⟧ → ⟦α⟧ → ⟦α⟧
  | ⟦⟧, ys => ys
  | x∷xs, ys => revcat xs (x∷ys)

def List.filter : (α → Bool) → ⟦α⟧ → ⟦α⟧
  | _, ⟦⟧ => ⟦⟧
  | p, x∷xs => let xs' := filter p xs
               if p x then x∷xs' else xs'

def List.All : (α → Bool) → ⟦α⟧ → Bool
  | _, ⟦⟧ => .true
  | p, x∷xs => p x and All p xs

def List.Any : (α → Bool) → ⟦α⟧ → Bool
  | _, ⟦⟧ => .false
  | p, x∷xs => p x or Any p xs

def List.doubleList : ⟦Nat⟧ → ⟦Nat⟧
  := Lmap Nat.double

def List.addNat : Nat → ⟦Nat⟧ → ⟦Nat⟧
  | n => Lmap (λx : Nat => x + n)

def List.multNat : Nat → ⟦Nat⟧ → ⟦Nat⟧
  | n => Lmap (λx : Nat => x * n)

def List.expNat : Nat → ⟦Nat⟧ → ⟦Nat⟧
  | n => Lmap (λx : Nat => x ^ n)

def List.enumTo : Nat → ⟦Nat⟧
  | .S n => append (.S n) (enumTo n)
  | _ => ⟦.O⟧

def List.replicate : Nat → α → ⟦α⟧
  | .O, _ => ⟦⟧
  | .S n, a => a∷replicate n a

def List.take : Nat → ⟦α⟧ → ⟦α⟧
  | .S n, x∷xs => x∷take n xs
  | _, _ => ⟦⟧

def List.takeWhile : (α → Bool) → ⟦α⟧ → ⟦α⟧
  | _, ⟦⟧ => ⟦⟧
  | p, x∷xs => let xs' := takeWhile p xs
               if p x then x∷xs' else ⟦⟧

def List.drop : Nat → ⟦α⟧ → ⟦α⟧
  | .S n, _∷xs => drop n xs
  | _, xs => xs

def List.dropWhile : (α → Bool) → ⟦α⟧ → ⟦α⟧
  | _, ⟦⟧ => ⟦⟧
  | p, xs@(x'∷xs') => if p x' then dropWhile p xs' else xs

def List.elemIndices : Nat → ⟦Nat⟧ → ⟦Nat⟧
  | n, x∷xs => let xs' := elemIndices n xs
               if n == x then .O∷addNat (.S .O) xs'
               else addNat (.S .O) xs'
  | _, _ => ⟦⟧

def List.pw : (α → β → γ) → ⟦α⟧ → ⟦β⟧ → ⟦γ⟧
  | op, x∷xs, y∷ys => (op x y)∷(pw op xs ys)
  | _, _, _ => ⟦⟧

def List.pwAdd : ⟦Nat⟧ → ⟦Nat⟧ → ⟦Nat⟧
  := pw (λx => λy => x + y)

def List.pwMult : ⟦Nat⟧ → ⟦Nat⟧ → ⟦Nat⟧
  := pw (λx => λy => x * y)

def List.isSorted : ⟦Nat⟧ → Bool
  | x∷xs@(x'∷_) => (x ≤ x') and isSorted xs
  | _ => .true

def List.minimum : ⟦Nat⟧ → Nat ⊕ Unit
  | n∷⟦⟧ => .inl n
  | n∷ns => .inl (Nat.min₂ n (Nat.stripMaybe (minimum ns)))
  | _ => .inr ()

def List.maximum : ⟦Nat⟧ → Nat
  | ⟦⟧ => .O
  | x∷xs => Nat.max₂ x (maximum xs)

def List.isPrefixOf : ⟦Nat⟧ → ⟦Nat⟧ → Bool
  | ⟦⟧, _ => .true
  | x∷xs, y∷ys => (x == y) and isPrefixOf xs ys
  | _, _ => .false

def List.mix : ⟦α⟧ → ⟦α⟧ → ⟦α⟧
  | x∷xs, y∷ys => x∷y∷mix xs ys
  | _, _ => ⟦⟧

def List.interspace : α → ⟦α⟧ → ⟦α⟧
  | _, ys@(_∷⟦⟧) => ys
  | x, y∷ys => y∷x∷interspace x ys
  | _, ⟦⟧ => ⟦⟧

-- Assume ordered lists
-- First element greater than n
def List.upper_bound : Nat → ⟦Nat⟧ → Nat
  | _, ⟦⟧ => .O
  | n, x∷xs => if n < x then x else upper_bound n xs

-- Assume ordered lists
-- First element not less than n
def List.lower_bound : Nat → ⟦Nat⟧ → Nat
  | _, ⟦⟧ => .O
  | n, x∷xs => if n ≤ x then x else lower_bound n xs
