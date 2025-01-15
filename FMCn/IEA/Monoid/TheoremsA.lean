import FMCn.IEA.Monoid.Definitions

open MagmaA SemigroupA MonoidA

theorem Opa_Only_Id [MonoidA M] :
  ∀ (u v : M), u é a (⊹)-identidade ∧ v é a (⊹)-identidade → u = v :=
by
  intro u v ⟨Hu, Hv⟩
  have huid : v ⊹ u = v ∧ u ⊹ v = v := by
    refine ⟨Hu.1 v, Hu.2 v⟩
  have hvid : u ⊹ v = u ∧ v ⊹ u = u := by
    refine ⟨Hv.1 u, Hv.2 u⟩
  rw [hvid.2] at huid
  exact huid.1

------------------------------------------------
-- PowA_Related Theorems :
------------------------------------------------

theorem Opa_PowA_R [MonoidA M] :
  ∀ (a : M) (n : Nat), a ⊹ (a ^ᴿ n) = (a ^ᴿ n) ⊹ a :=
by
  intro a n
  induction n with
  | zero => rw [PowA_R, id_opa, opa_id]
  | succ k HI => rw [PowA_R, HI, ← opa_ass, ← HI]

theorem Opa_Pow_Eq [MonoidA M] :
  ∀ (a : M) (n : Nat), a ^ᴿ n = a ^ᴸ n :=
by
  intro a n
  induction n with
  | zero => rw [PowA_R, PowA_L]
  | succ k HI => rw [PowA_L, ← HI, PowA_R, Opa_PowA_R]

theorem Opa_Pow_Sum [MonoidA M] :
  ∀ (a : M) (n m : Nat), a ^ᴿ (n + m) = (a ^ᴿ n) ⊹ (a ^ᴿ m) :=
by
  intro a n m
  induction m with
  | zero => rw [Nat.add_zero, PowA_R, opa_id]
  | succ k HI => rw [Nat.add_succ, PowA_R, HI, PowA_R,
                     ← opa_ass, Opa_PowA_R, opa_ass]

theorem Opa_Pow_Pow [MonoidA M] :
  ∀ (a : M) (n m : Nat), (a ^ᴿ n) ^ᴿ m = a ^ᴿ (n * m) :=
by
  intro a n m
  induction m with
  | zero => rw [PowA_R, Nat.mul_zero, PowA_R]
  | succ k HI => rw [PowA_R, Nat.mul_succ,
                     Opa_Pow_Sum, ← HI, Opa_PowA_R]

theorem Opa_Pow_Id [MonoidA M] :
  ∀ (n : Nat), z ^ᴿ n = (z : M) :=
by
  intro n
  induction n with
  | zero => rw [PowA_R]
  | succ k HI => rw [PowA_R, HI, opa_id]
