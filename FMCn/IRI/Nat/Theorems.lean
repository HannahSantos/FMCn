import FMCn.IRI.Nat.Definitions
import FMCn.Intro_Lang_Proofs
import FMCn.CFR1.Useful
import FMCn.IEA.Monoid.Definitions

namespace data

open Nat

----------------------------------------------------------
-- Succ-Inj:
----------------------------------------------------------
theorem zero_ne_succ :
  ∀ (n : Nat), O ≠ S n :=
by
  intro n h
  cases h -- Magia?

theorem pred_succ :
  ∀ (n : Nat), pred (S n) = n :=
by
  intro n
  rw [pred]

theorem succ_inj :
  ∀ (n m : Nat), S n = S m → n = m :=
by
  intro n m h
  have hp : pred (S n) = pred (S m) := univ pred h
  rw [pred_succ, pred_succ] at hp
  exact hp

----------------------------------------------------------
-- Soma:
----------------------------------------------------------

theorem add_zero :
  ∀ (n : Nat), n + O = n :=
by
  intro n
  rw [add]

theorem zero_add :
  ∀ (n : Nat), O + n = n :=
by
  intro n
  induction n with
  | O => rw [add_zero]
  | S k HI => rw [add, HI]

theorem succ_add :
  ∀ (n m : Nat), (S n) + m = S (n + m) :=
by
  intro n m
  induction m with
  | O => rw [add, add]
  | S k HI => rw [add, add, HI]

theorem add_ass :
  ∀ (n m k : Nat), (n + m) + k = n + (m + k) :=
by
  intro n m k
  induction k with
  | O => rw [add, add]
  | S k HI => rw [add, add, add, HI]

----------------------------------------------------------
-- (Nat, +, O) é um Monoid
----------------------------------------------------------

instance : MonoidA Nat where
  opa := uncurry add
  z := O
  opa_ass := add_ass
  opa_id := add_zero
  id_opa := zero_add

theorem add_com :
  ∀ (n m : Nat), n + m = m + n :=
by
  intro n m
  induction m with
  | O => rw [add, zero_add]
  | S k HI => rw [add, HI, succ_add]

theorem cancel_add :
  ∀ (n m k : Nat), k + n = k + m → n = m :=
by
  intro n m k h
  induction k with
  | O => rw [zero_add n, zero_add m] at h
         exact h
  | S k HI => rw [succ_add k n, succ_add k m] at h
              exact HI (succ_inj (k + n) (k + m) h)

----------------------------------------------------------
-- Produto:
----------------------------------------------------------

theorem mul_one :
  ∀ (n : Nat), n * (S O) = n :=
by
  intro n
  rw [mul, mul, zero_add]

theorem zero_mul :
  ∀ (n : Nat), O * n = O :=
by
  intro n
  induction n with
  | O => rw [mul]
  | S k HI => rw [mul, HI, add]

theorem succ_mul :
  ∀ (n m : Nat), (S n) * m = (n * m) + m :=
by
  intro n m
  induction m with
  | O => rw [mul, mul, add]
  | S k HI => rw [mul, HI, mul, add,
                  add, add_ass, add_com k n,
                  ← add_ass]

theorem mul_com :
  ∀ (n m : Nat), n * m = m * n :=
by
  intro n m
  induction m with
  | O => rw [mul, zero_mul]
  | S k HI => rw [mul, HI, succ_mul]

theorem one_mul :
  ∀ (n : Nat), (S O) * n = n :=
by
  intro n
  rw [mul_com, mul_one]

theorem distrL :
  ∀ (k n m : Nat), k * (n + m) = (k * n) + (k * m) :=
by
  intro k n m
  induction k with
  | O => rw [zero_mul, zero_mul, zero_mul, add]
  | S k HI => rw [succ_mul, HI, succ_mul, succ_mul,
                  add_ass (k * n) n (k * m + m),
                  add_com n (k * m + m),
                  add_ass (k * m) m n, add_ass,
                  add_com m n]

theorem distrR :
  ∀ (n m k : Nat), (n + m) * k = (n * k) + (m * k) :=
by
  intro n m k
  rw [mul_com, mul_com n k, mul_com m k, distrL]

theorem mul_ass :
  ∀ (n m k : Nat), (n * m) * k = n * (m * k) :=
by
  intro n m k
  induction k with
  | O => rw [mul, mul, mul]
  | S k HI => rw [mul, HI, mul, distrL]

----------------------------------------------------------
-- (Nat, *, SO) é um Monoid
----------------------------------------------------------
instance : MonoidM Nat where
  opm := uncurry mul
  opm_ass := mul_ass
  e := S O
  id_opm := one_mul
  opm_id := mul_one

----------------------------------------------------------
-- Exponenciação:
----------------------------------------------------------

theorem pow_one :
  ∀ (n : Nat), n ^ (S O) = n :=
by
  intro n
  rw [pow, pow, one_mul]

theorem pow_add_mul_pow :
  ∀ (n m k : Nat), n ^ (m + k) = (n ^ m) * (n ^ k) :=
by
  intro n m k
  induction k with
  | O => rw [add, pow, mul_one]
  | S k HI => rw [add, pow, HI, pow, mul_ass]

theorem pow_pow_pow_mul :
  ∀ (n m k : Nat), (n ^ m) ^ k = n ^  (m * k) :=
by
  intro n m k
  induction k with
  | O => rw [mul, pow, pow]
  | S k HI => rw [pow, HI, mul, pow_add_mul_pow]

theorem pow_two :
  ∀ (n : Nat), n ^ (S (S O)) = n * n :=
by
  intro n
  rw [pow, pow, pow, one_mul]
/-
theorem Pow_No_Id_L :
  ¬∃ (x : Nat), ∀ (n : Nat), x ^ n = n :=
by
  intro h
  apply h.elim
  intro a
  apply demorgan_forall_converse
  refine ⟨S (S O), ?_⟩
  intro ha
  induction a with
  | O => rw [pow, mul] at ha
         exact zero_ne_succ (S O) ha
  | S k HI => rw [pow, pow_one, mul, add, succ_mul,
                  ← pow_two] at ha
              have ha' : (k ^ S (S O)) + k + k = S O :=
                succ_inj ((k ^ S (S O)) + k + k) (S O) ha
              rw [] at ha'
-/
