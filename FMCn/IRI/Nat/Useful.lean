import FMCn.IRI.Nat.Definitions
import FMCn.CFR1.Useful

namespace data

open Nat

----------------------------------------------------------
-- Succ-Inj:
----------------------------------------------------------

theorem zero_ne_succ {n : Nat}:
  O ≠ S n :=
by
  intro h
  cases h -- Magia?

theorem pred_succ :
  ∀ (n : Nat), pred (S n) = n :=
by
  intro n
  rw [pred]

theorem succ_inj {n m : Nat}:
  S n = S m → n = m :=
by
  intro h
  have hp : pred (S n) = pred (S m) := univ pred h
  rw [pred_succ, pred_succ] at hp
  exact hp

----------------------------------------------------------
-- Add :
----------------------------------------------------------

theorem add_zero :
  ∀ (n : Nat), n + O = n :=
by
  intro n
  rw [add]

theorem add_succ :
  ∀ (n m : Nat), n + (S m) = S (n + m) :=
by
  intro n m
  rw [add]

----------------------------------------------------------
-- Mul :
----------------------------------------------------------

theorem mul_zero :
  ∀ (n : Nat), n * O = O :=
by
  intro n
  rw [mul]

theorem mul_succ :
  ∀ (n m : Nat), n * (S m) = (n * m) + n :=
by
  intro n m
  rw [mul]

----------------------------------------------------------
-- Pow :
----------------------------------------------------------

theorem pow_zero :
  ∀ (n : Nat), n ^ O = S O :=
by
  intro n
  rw [pow]

theorem pow_succ :
  ∀ (n m : Nat), n ^ (S m) = (n ^ m) * n :=
by
  intro n m
  rw [pow]

----------------------------------------------------------
-- Max :
----------------------------------------------------------

theorem max_zero {a : Nat} :
  max₂ a O = a :=
by
  cases a with
  | O => rw [max₂]
  | S k => rw [max₂]
           intro h
           exact zero_ne_succ h.symm

theorem zero_max {a : Nat} :
  max₂ O a = a :=
by
  rw [max₂]

theorem max_succ {a b : Nat} :
  max₂ (S a) (S b) = S (max₂ a b) :=
by
  rw [max₂]
