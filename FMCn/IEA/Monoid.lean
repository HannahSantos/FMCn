import FMCn.IEA.Definitions

open has_Op has_Id has_Inv Semigroup Monoid

theorem Op_Only_Id [Monoid M] :
  ∀ (u v : M), u é a identidade ∧ v é a identidade → u = v :=
by
  intro u v ⟨Hu, Hv⟩
  have huid : v ⋆ u = v ∧ u ⋆ v = v := by
    refine ⟨Hu.1 v, Hu.2 v⟩
  have hvid : u ⋆ v = u ∧ v ⋆ u = u := by
    refine ⟨Hv.1 u, Hv.2 u⟩
  rw [hvid.2] at huid
  exact huid.1

------------------------------------------------
-- Pow_Related Theorems :
------------------------------------------------

theorem Op_Pow_R [Monoid M] :
  ∀ (a : M) (n : Nat), a ⋆ (a ↑ᴿ n) = (a ↑ᴿ n) ⋆ a :=
by
  intro a n
  induction n with
  | zero => rw [Pow_R, Id_Op, Op_Id]
  | succ k HI => rw [Pow_R, HI, ← Op_Ass, ← HI]

theorem Op_Pow_Eq [Monoid M] :
  ∀ (a : M) (n : Nat), a ↑ᴿ n = a ↑ᴸ n :=
by
  intro a n
  induction n with
  | zero => rw [Pow_R, Pow_L]
  | succ k HI => rw [Pow_L, ← HI, Pow_R, Op_Pow_R]

theorem Op_Pow_Sum [Monoid M] :
  ∀ (a : M) (n m : Nat), a ↑ᴿ (n + m) = (a ↑ᴿ n) ⋆ (a ↑ᴿ m) :=
by
  intro a n m
  induction m with
  | zero => rw [Nat.add_zero, Pow_R, Op_Id]
  | succ k HI => rw [Nat.add_succ, Pow_R, HI, Pow_R,
                     ← Op_Ass, Op_Pow_R, Op_Ass]

theorem Op_Pow_Pow [Monoid M] :
  ∀ (a : M) (n m : Nat), (a ↑ᴿ n) ↑ᴿ m = a ↑ᴿ (n * m) :=
by
  intro a n m
  induction m with
  | zero => rw [Pow_R, Nat.mul_zero, Pow_R]
  | succ k HI => rw [Pow_R, Nat.mul_succ,
                     Op_Pow_Sum, ← HI, Op_Pow_R]

theorem Op_Pow_Id [Monoid M] :
  ∀ (n : Nat), e ↑ᴿ n = (e : M) :=
by
  intro n
  induction n with
  | zero => rw [Pow_R]
  | succ k HI => rw [Pow_R, HI, Op_Id]
