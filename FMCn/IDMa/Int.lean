import FMCn.IDMa.axioms

theorem ZA_IdL :
  ∀ (a : Int), 0 + a = a :=
by
  intro a
  rw [ZA_Com, ZA_IdR]
