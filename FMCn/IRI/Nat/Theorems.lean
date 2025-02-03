import FMCn.IRI.Nat.Definitions
import FMCn.IRI.Nat.Useful
import FMCn.Intro_Lang_Proofs
import FMCn.CFR1.Definitions
import FMCn.CFR1.Useful
import FMCn.IEA.Monoid.Definitions
import FMCn.IEA.Monoid.TheoremsA
import FMCn.IRI.Bool.Theorems

namespace data

open Nat

----------------------------------------------------------
-- Soma:
----------------------------------------------------------

theorem zero_add :
  ∀ (n : Nat), O + n = n :=
by
  intro n
  induction n with
  | O => rw [add_zero]
  | S k HI => rw [add_succ, HI]

theorem succ_add :
  ∀ (n m : Nat), (S n) + m = S (n + m) :=
by
  intro n m
  induction m with
  | O => rw [add_zero, add_zero]
  | S k HI => rw [add_succ, add_succ, HI]

theorem add_ass :
  ∀ (n m k : Nat), (n + m) + k = n + (m + k) :=
by
  intro n m k
  induction k with
  | O => rw [add_zero, add_zero]
  | S k HI => rw [add_succ, add_succ, add_succ, HI]

----------------------------------------------------------
-- (Nat, +, O) é um Monoid
----------------------------------------------------------

instance : MonoidA Nat where
  opa := uncurry add
  z := O
  opa_ass := add_ass
  opa_id := add_zero
  id_opa := zero_add

theorem add_zero_id :
  O é a (⊹)-identidade :=
by
  refine⟨add_zero, zero_add⟩

theorem add_com :
  ∀ (n m : Nat), n + m = m + n :=
by
  intro n m
  induction m with
  | O => rw [add_zero, zero_add]
  | S k HI => rw [add_succ, HI, succ_add]

theorem cancel_add :
  ∀ (n m k : Nat), k + n = k + m → n = m :=
by
  intro n m k h
  induction k with
  | O => rw [zero_add n, zero_add m] at h
         exact h
  | S k HI => rw [succ_add k n, succ_add k m] at h
              exact HI (succ_inj h)

theorem add_null {n m : Nat} :
  n + m = n → m = O :=
by
  intro h
  induction n with
  | O => rw [zero_add] at h
         exact h
  | S k HI => rw [succ_add] at h
              exact HI (succ_inj h)

theorem null_add {n m : Nat} :
  m + n = n → m = O :=
by
  intro h
  rw [add_com] at h
  exact add_null h

theorem left_add_to_zero {n m : Nat} :
  n + m = O → n = O :=
by
  intro h
  cases m with
  | O => rw [add_zero] at h
         exact h
  | S k => rw [add_succ] at h
           exact False.elim (zero_ne_succ h.symm)

theorem right_add_to_zero {n m : Nat} :
  n + m = O → m = O :=
by
  intro h
  rw [add_com] at h
  exact left_add_to_zero h

----------------------------------------------------------
-- Produto:
----------------------------------------------------------

theorem mul_one :
  ∀ (n : Nat), n * (S O) = n :=
by
  intro n
  rw [mul_succ, mul_zero, zero_add]

theorem zero_mul :
  ∀ (n : Nat), O * n = O :=
by
  intro n
  induction n with
  | O => rw [mul_zero]
  | S k HI => rw [mul_succ, HI, add_zero]

theorem succ_mul :
  ∀ (n m : Nat), (S n) * m = (n * m) + m :=
by
  intro n m
  induction m with
  | O => rw [mul_zero, mul_zero, add_zero]
  | S k HI => rw [mul_succ, HI, mul_succ, add_succ,
                  add_succ, add_ass, add_com k n,
                  ← add_ass]

theorem mul_com :
  ∀ (n m : Nat), n * m = m * n :=
by
  intro n m
  induction m with
  | O => rw [mul_zero, zero_mul]
  | S k HI => rw [mul_succ, HI, succ_mul]

theorem one_mul :
  ∀ (n : Nat), (S O) * n = n :=
by
  intro n
  rw [mul_com, mul_one]

theorem mul_two :
  ∀ (n : Nat), n * (S (S O)) = n + n :=
by
  intro n
  rw [mul_succ, mul_one]

theorem distrL :
  ∀ (k n m : Nat), k * (n + m) = (k * n) + (k * m) :=
by
  intro k n m
  induction k with
  | O => rw [zero_mul, zero_mul, zero_mul, add_zero]
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
  | O => rw [mul_zero, mul_zero, mul_zero]
  | S k HI => rw [mul_succ, HI, mul_succ, distrL]

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
  rw [pow_succ, pow_zero, one_mul]

theorem one_pow :
  ∀ (n : Nat), (S O) ^ n = (S O) :=
by
  intro n
  induction n with
  | O => rw [pow_zero]
  | S k HI => rw [pow_succ, mul_one, HI]

theorem zero_pow :
  ∀ (n : Nat), n ≠ O → O ^ n = O :=
by
  intro n h
  cases n with
  | O => exact False.elim (h rfl)
  | S k => rw [pow_succ, mul_zero]

theorem pow_add_mul_pow :
  ∀ (n m k : Nat), n ^ (m + k) = (n ^ m) * (n ^ k) :=
by
  intro n m k
  induction k with
  | O => rw [add_zero, pow_zero, mul_one]
  | S k HI => rw [add_succ, pow_succ, HI,
                  pow_succ, mul_ass]

theorem pow_pow_pow_mul :
  ∀ (n m k : Nat), (n ^ m) ^ k = n ^  (m * k) :=
by
  intro n m k
  induction k with
  | O => rw [mul_zero, pow_zero, pow_zero]
  | S k HI => rw [pow_succ, HI, mul_succ,
                  pow_add_mul_pow]

theorem pow_two :
  ∀ (n : Nat), n ^ (S (S O)) = n * n :=
by
  intro n
  rw [pow_succ, pow_one]
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

----------------------------------------------------------
-- Relação ≥ :
----------------------------------------------------------

theorem geq_bottom :
  ∀ (a : Nat), a ≥ O :=
by
  intro a
  apply Exists.intro a
  rw [zero_add]

theorem zero_geq {a : Nat} :
  O ≥ a → a = O :=
by
  intro h
  cases a with
  | O => rfl
  | S k => apply h.elim
           intro x hx
           rw [succ_add] at hx
           exact False.elim (zero_ne_succ hx.symm)

theorem geq_succ_self {a : Nat} :
  S a ≥ a :=
by
  apply Exists.intro (S O)
  rw [add_succ, add_zero]

theorem geq_succ {a b : Nat} :
  a ≥ b → S a ≥ S b :=
by
  intro h
  apply h.elim
  intro x hx
  apply Exists.intro x
  rw [succ_add, hx]

theorem succ_geq {a b : Nat} :
  S a ≥ S b → a ≥ b :=
by
  intro h
  apply h.elim
  intro x hx
  rw [succ_add] at hx
  refine ⟨x, succ_inj hx⟩

theorem geq_refl :
  geq é reflexiva :=
by
  intro a
  refine ⟨O, add_zero a⟩

theorem geq_trans :
  geq é transitiva :=
by
  intro a b c hab hbc
  apply hab.elim
  intro x hx
  apply hbc.elim
  intro y hy
  have hyx : c + (y + x) = a := by
    rw [← add_ass, hy, hx]
  refine ⟨(y + x), hyx⟩

theorem geq_antisymm :
  geq é antissimétrica :=
by
  intro a b hab hba
  apply hab.elim
  intro x hx
  apply hba.elim
  intro y hy
  rw [← hy, add_ass] at hx
  have h : y = O := left_add_to_zero (add_null hx)
  rw [h, add_zero] at hy
  exact hy

theorem geq_total :
  geq é total :=
by
  intro a
  induction a with
  | O => intro b
         apply Or.inr (geq_bottom b)
  | S k HI =>
    intro b
    cases b with
    | O => apply Or.inl (geq_bottom (S k))
    | S b => have h : k ≥ b ∨ b ≥ k := HI b
             apply h.elim
             · intro hkb
               apply Or.inl (geq_succ hkb)
             · intro hbk
               apply Or.inr (geq_succ hbk)

theorem geq_add {a b c d : Nat} :
  a ≥ c ∧ b ≥ d → (a + b) ≥ (c + d) :=
by
  intro ⟨hac, hbd⟩
  apply hac.elim
  intro x hx
  apply hbd.elim
  intro y hy
  refine ⟨(x + y), ?_⟩
  · rw [add_ass, ← add_ass d x y,
        add_com d x, add_ass, hy,
        ← add_ass, hx]

theorem geq_mul {a b d : Nat} :
  ∀ (c : Nat), a ≥ c ∧ b ≥ d → (a * b) ≥ (c * d) :=
by
  induction a with
  | O => intro c ⟨hac, _⟩
         rw [zero_geq hac, zero_mul, zero_mul]
         apply geq_refl
  | S k HI =>
    intro c ⟨hkc, hbd⟩
    cases c with
    | O => rw [zero_mul]
           apply geq_bottom
    | S c => rw [succ_mul, succ_mul]
             apply geq_add
             exact ⟨HI c (⟨succ_geq hkc, hbd⟩), hbd⟩

theorem ne_zero_geq_one {a : Nat} :
  a ≠ O → a ≥ S O :=
by
  intro h
  cases a with
  | O => exact False.elim (h rfl)
  | S k => apply geq_succ
           apply geq_bottom

theorem pow_geq_one {a b : Nat} :
  a ≠ O → (a ^ b) ≥ (S O) :=
by
  intro h
  induction b with
  | O => rw [pow_zero]
         apply geq_refl
  | S k HI => rw [pow_succ, ← mul_one (S O)]
              exact geq_mul (S O) ⟨HI, ne_zero_geq_one h⟩

theorem geq_pow {a b c : Nat} :
  a ≠ O ∧ b ≥ c → (a ^ b) ≥ (a ^ c) :=
by
  intro ⟨ha, hc⟩
  apply hc.elim
  intro k hk
  rw [← hk, pow_add_mul_pow, ← mul_one (a ^ c),
      mul_ass, one_mul]
  apply geq_mul
  refine ⟨?_, ?_⟩
  · apply geq_refl
  · exact pow_geq_one ha

theorem zero_ne_geq_succ {n : Nat} :
  ¬ O ≥ S n :=
by
  intro h
  apply h.elim
  intro x hx
  rw [succ_add] at hx
  exact zero_ne_succ hx.symm

theorem leq_correctness {b : Nat} :
  ∀ (a : Nat), a ≥ b ↔ (b ≤ a) = .true :=
by
  induction b with
  | O => intro a
         rw [leq]
         refine ⟨?_, ?_⟩
         · intro _
           rfl
         · intro _
           exact geq_bottom a
  | S k HI =>
    intro a
    cases a with
    | O => rw [leq]
           refine ⟨?_, ?_⟩
           · intro h
             exact False.elim (zero_ne_geq_succ h)
           · intro h
             exact False.elim (false_neq_true h)
           intro h
           exact zero_ne_succ h.symm
    | S a => rw [leq]
             refine ⟨?_, ?_⟩
             · intro h
               exact (HI a).1 (succ_geq h)
             · intro h
               exact geq_succ ((HI a).2 h)

----------------------------------------------------------
-- Max :
----------------------------------------------------------

theorem max_opt :
  ∀ (a b : Nat), max₂ a b = a ∨ max₂ a b = b :=
by
  intro a
  induction a with
  | O => intro b
         rw [zero_max]
         apply Or.inr rfl
  | S k HI =>
    intro b
    cases b with
    | O => rw [max_zero]
           apply Or.inl rfl
    | S b => have h : max₂ k b = k ∨ max₂ k b = b := HI b
             apply h.elim
             · intro hk
               rw [max_succ, hk]
               apply Or.inl rfl
             · intro hb
               rw [max_succ, hb]
               apply Or.inr rfl

theorem max_com {a : Nat} :
  ∀ (b : Nat), max₂ a b = max₂ b a :=
by
  induction a with
  | O => intro b
         rw [max_zero, zero_max]
  | S k HI => intro b
              cases b with
              | O => rw [max_zero, zero_max]
              | S b => rw [max_succ, max_succ, HI b]

theorem max_succ_ne_zero {b : Nat} :
  max₂ O (S b) ≠ O :=
by
  intro h
  rw [zero_max] at h
  exact zero_ne_succ h.symm

theorem max_is_zero {b : Nat} :
  max₂ O b = O → b = O :=
by
  rw [zero_max]
  exact impl_refl (b = O)

theorem max_impl_succ :
  ∀ (a b : Nat), max₂ a b = a → max₂ (S a) b = S a :=
by
  intro a
  induction a with
  | O => intro b h
         rw [max_is_zero h, max_zero]
  | S k HI =>
    intro b h
    cases b with
    | O => rw [max_zero]
    | S b => rw [max_succ] at h
             rw [max_succ]
             have h' : max₂ k b = k := succ_inj h
             rw [HI b h']

theorem max_succ_arg {a b : Nat} :
  max₂ a (S b) = a → max₂ a b = a :=
by
  intro h
  cases a with
  | O => exact False.elim (max_succ_ne_zero h)
  | S k => rw [max_succ] at h
           have h' : max₂ k b = k := succ_inj h
           exact max_impl_succ k b h'

theorem max_geq {a : Nat} :
  ∀ (b : Nat), max₂ a b = a → a ≥ b :=
by
  induction a with
  | O => intro b h
         rw [max_is_zero h]
         apply geq_refl
  | S k HI =>
    intro b h
    cases b with
    | O => exact geq_bottom (S k)
    | S b => rw [max_succ] at h
             have h' : k ≥ b := HI b (succ_inj h)
             exact geq_succ h'

--------------------------------------------------------

theorem geq_simp {n m k u v : Nat} (h : max₂ n m = n)
  (H1 : (k ^ n) ≥ u) (H2 : (k ^ m) ≥ v) (h' : k ≠ O ) :
  (k ^ max₂ n m + k ^ max₂ n m) ≥ (u + v) :=
by
  rw [h]
  apply geq_add
  refine ⟨H1, ?_⟩
  apply geq_trans (k ^ n) (k ^ m) v
  · apply geq_pow
    refine ⟨?_, max_geq m h⟩
    · exact h'
  · exact H2
