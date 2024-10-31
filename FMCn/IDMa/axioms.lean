axiom ZA_IdR : ∀ (a : Int), a + 0 = a
axiom ZA_InvR : ∀ (a : Int), a + (-a) = 0
axiom ZA_Ass : ∀ (a b c : Int), a + b + c = a + (b + c)
axiom ZA_Com : ∀ (a b : Int), a + b = b + a
axiom ZM_IdR : ∀ (a : Int), a * 1 = a
axiom ZM_Ass : ∀ (a b c : Int), a * b * c = a * (b * c)
axiom ZM_Com : ∀ (a b : Int), a * b = b * a
axiom Z_DistR : ∀ (a b c : Int), (a + b) * c = a * c + b * c
