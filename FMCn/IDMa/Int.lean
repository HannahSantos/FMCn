import FMCn.IDMa.axioms

theorem ZA_IdL :
  ∀ (a : Int), 0 + a = a :=
by
  intro a
  rw [ZA_Com 0 a, ZA_IdR a]

theorem ZA_InvL :
  ∀ (a : Int), -a + a = 0 :=
by
  intro a
  rw [ZA_Com (-a) a, ZA_InvR a]
