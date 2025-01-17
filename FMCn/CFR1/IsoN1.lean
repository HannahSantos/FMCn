import FMCn.CFR1.Definitions
import FMCn.CFR1.Useful
import FMCn.IRI.Nat.Definitions

namespace data

open Nat
------------------------------------------------
-- iso (N + 1) N
------------------------------------------------

def F :  Nat → Nat ⊕ 𝟙
  | O => .inr ()
  | S n => .inl n

def G: Nat ⊕ 𝟙 → Nat
  | .inr _ => O
  | .inl n => S n

theorem iso_nat_unit:
  (Nat ⊕ 𝟙) ≅ Nat :=
by
  refine ⟨G, F, ?_, ?_⟩
  · funext x
    rw [comp_def, F, G]
    cases x with
    | O => rfl
    | S n => rfl
  · funext y
    rw [comp_def, G, F]
    cases y with
    | inl n => rfl
    | inr unit => rfl
