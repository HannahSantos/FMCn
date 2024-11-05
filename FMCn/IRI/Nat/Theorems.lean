import FMCn.IRI.Nat.Definitions
import FMCn.Intro_Lang_Proofs
import FMCn.CFR1.Useful

namespace data

open Nat

----------------------------------------------------------
-- Succ-Inj:
----------------------------------------------------------

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

theorem Add_zero_L :
  ∀ (n : Nat), O + n = n :=
by
  intro n
  induction n with
  | O => rw [add]
  | S k HI => rw [add, HI]

theorem Add_succ_L :
  ∀ (n m : Nat), (S n) + m = S (n + m) :=
by
  intro n m
  induction m with
  | O => rw [add, add]
  | S k HI => rw [add, add, HI]

theorem Add_Ass :
  ∀ (n m k : Nat), (n + m) + k = n + (m + k) :=
by
  intro n m k
  induction k with
  | O => rw [add, add]
  | S k HI => rw [add, add, add, HI]

theorem Add_Com :
  ∀ (n m : Nat), n + m = m + n :=
by
  intro n m
  induction m with
  | O => rw [add, Add_zero_L]
  | S k HI => rw [add, HI, Add_succ_L]

theorem Add_CanL :
  ∀ (n m k : Nat), k + n = k + m → n = m :=
by
  intro n m k h
  induction k with
  | O => rw [Add_zero_L n, Add_zero_L m] at h
         exact h
  | S k HI => rw [Add_succ_L k n, Add_succ_L k m] at h
              exact HI (succ_inj (k + n) (k + m) h)

----------------------------------------------------------
-- Produto:
----------------------------------------------------------

theorem Mul_Id_R :
  ∀ (n : Nat), n * (S O) = n :=
by
  intro n
  rw [mul, mul, Add_zero_L]

theorem Mul_zero_L :
  ∀ (n : Nat), O * n = O :=
by
  intro n
  induction n with
  | O => rw [mul]
  | S k HI => rw [mul, HI, add]

theorem Mul_succ_L :
  ∀ (n m : Nat), (S n) * m = (n * m) + m :=
by
  intro n m
  induction m with
  | O => rw [mul, mul, add]
  | S k HI => rw [mul, HI, mul, add,
                  add, Add_Ass, Add_Com k n,
                  ← Add_Ass]

theorem Mul_Com :
  ∀ (n m : Nat), n * m = m * n :=
by
  intro n m
  induction m with
  | O => rw [mul, Mul_zero_L]
  | S k HI => rw [mul, HI, Mul_succ_L]

theorem Mul_Id_L :
  ∀ (n : Nat), (S O) * n = n :=
by
  intro n
  rw [Mul_Com, Mul_Id_R]

theorem Distr_L :
  ∀ (k n m : Nat), k * (n + m) = (k * n) + (k * m) :=
by
  intro k n m
  induction k with
  | O => rw [Mul_zero_L, Mul_zero_L, Mul_zero_L, add]
  | S k HI => rw [Mul_succ_L, HI, Mul_succ_L, Mul_succ_L,
                  Add_Ass (k * n) n (k * m + m),
                  Add_Com n (k * m + m),
                  Add_Ass (k * m) m n, Add_Ass,
                  Add_Com m n]

theorem Distr_R :
  ∀ (n m k : Nat), (n + m) * k = (n * k) + (m * k) :=
by
  intro n m k
  rw [Mul_Com, Mul_Com n k, Mul_Com m k, Distr_L]

theorem Mul_Ass :
  ∀ (n m k : Nat), (n * m) * k = n * (m * k) :=
by
  intro n m k
  induction k with
  | O => rw [mul, mul, mul]
  | S k HI => rw [mul, HI, mul, Distr_L]

----------------------------------------------------------
-- Exponenciação:
----------------------------------------------------------

theorem Pow_Id_R :
  ∀ (n : Nat), n ^ (S O) = n :=
by
  intro n
  rw [pow, pow, Mul_Id_L]

theorem Pow_Add_eq_Mul_Pow :
  ∀ (n m k : Nat), n ^ (m + k) = (n ^ m) * (n ^ k) :=
by
  intro n m k
  induction k with
  | O => rw [add, pow, Mul_Id_R]
  | S k HI => rw [add, pow, HI, pow, Mul_Ass]

theorem Pow_Pow_eq_Pow_Mul :
  ∀ (n m k : Nat), (n ^ m) ^ k = n ^  (m * k) :=
by
  intro n m k
  induction k with
  | O => rw [mul, pow, pow]
  | S k HI => rw [pow, HI, mul, Pow_Add_eq_Mul_Pow]

theorem Pow_two_eq_Mul_self :
  ∀ (n : Nat), n ^ (S (S O)) = n * n :=
by
  intro n
  rw [pow, pow, pow, Mul_Id_L]
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
  cases a with
  | O => rw [pow, mul] at ha
         exact peano_neg (S O) ha
  | S k => rw [pow, Pow_Id_R, mul, add, Mul_succ_L,
               ← Pow_two_eq_Mul_self] at ha
           have ha' : (k ^ S (S O)) + k + k = S O :=
-/
