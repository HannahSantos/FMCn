import FMCn.IEA.Monoid.Definitions

open MagmaM SemigroupM MonoidM

theorem Opm_Only_Id [MonoidM M] :
  ∀ (u v : M), u é a (⋆)-identidade ∧ v é a (⋆)-identidade → u = v :=
by
  intro u v ⟨Hu, Hv⟩
  have huid : v ⋆ u = v ∧ u ⋆ v = v := by
    refine ⟨Hu.1 v, Hu.2 v⟩
  have hvid : u ⋆ v = u ∧ v ⋆ u = u := by
    refine ⟨Hv.1 u, Hv.2 u⟩
  rw [hvid.2] at huid
  exact huid.1

------------------------------------------------
-- PowM_Related Theorems :
------------------------------------------------

theorem Opm_PowM_R [MonoidM M] :
  ∀ (a : M) (n : Nat), a ⋆ (a ↑ᴿ n) = (a ↑ᴿ n) ⋆ a :=
by
  intro a n
  induction n with
  | zero => rw [PowM_R, id_opm, opm_id]
  | succ k HI => rw [PowM_R, HI, ← opm_ass, ← HI]

theorem Opm_Pow_Eq [MonoidM M] :
  ∀ (a : M) (n : Nat), a ↑ᴿ n = a ↑ᴸ n :=
by
  intro a n
  induction n with
  | zero => rw [PowM_R, PowM_L]
  | succ k HI => rw [PowM_L, ← HI, PowM_R, Opm_PowM_R]

theorem Opm_Pow_Sum [MonoidM M] :
  ∀ (a : M) (n m : Nat), a ↑ᴿ (n + m) = (a ↑ᴿ n) ⋆ (a ↑ᴿ m) :=
by
  intro a n m
  induction m with
  | zero => rw [Nat.add_zero, PowM_R, opm_id]
  | succ k HI => rw [Nat.add_succ, PowM_R, HI, PowM_R,
                     ← opm_ass, Opm_PowM_R, opm_ass]

theorem Opm_Pow_Pow [MonoidM M] :
  ∀ (a : M) (n m : Nat), (a ↑ᴿ n) ↑ᴿ m = a ↑ᴿ (n * m) :=
by
  intro a n m
  induction m with
  | zero => rw [PowM_R, Nat.mul_zero, PowM_R]
  | succ k HI => rw [PowM_R, Nat.mul_succ,
                     Opm_Pow_Sum, ← HI, Opm_PowM_R]

theorem Opm_Pow_Id [MonoidM M] :
  ∀ (n : Nat), e ↑ᴿ n = (e : M) :=
by
  intro n
  induction n with
  | zero => rw [PowM_R]
  | succ k HI => rw [PowM_R, HI, opm_id]
