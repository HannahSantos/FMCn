namespace data

inductive List (α : Type) where
  | Nil : List α
  | Cons : α → List α → List α
  deriving Repr

infixr:65 "∷" => List.Cons
notation:70 "‖" α "‖" => List α
notation:70 "⟦⟧" => List.Nil

open List
