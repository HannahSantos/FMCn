import FMCn.IEA.Group.Definitions
import FMCn.IEA.Monoid.TheoremsA
import FMCn.CFR1.Useful

open MagmaA SemigroupA MonoidA GroupA

------------------------------------------------
-- GroupA Theorems (Easy/Basic) :
------------------------------------------------

theorem Opa_Can_R [GroupA G] :
  ∀ (a b c : G), a ⊹ c = b ⊹ c → a = b :=
by
  intro a b c h
  have h1 :  a ⊹ c ⊹ −c = b ⊹ c ⊹ −c := by
    exact data.univ (· ⊹ −c) h
  rw [opa_ass, opa_ainv, opa_ass, opa_ainv, opa_id, opa_id] at h1
  exact h1

theorem Opa_Can_L [GroupA G] :
  ∀ (a b c : G), c ⊹ a = c ⊹ b → a = b :=
by
  intro a b c h
  have h1 :  −c ⊹ (c ⊹ a) = −c ⊹ (c ⊹ b) := by
    exact data.univ (−c ⊹ ·) h
  rw [← opa_ass, ainv_opa, ← opa_ass, ainv_opa, id_opa, id_opa] at h1
  exact h1

theorem Ida_Exists_for_all [GroupA G] (i : G):
  (∃ (x : G), i ⊹ x = x ∧ x ⊹ i = x) → i é a (⊹)-identidade :=
by
  intro h
  apply h.elim
  intro x ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · intro a
    apply Opa_Can_R (opa (a, i)) a x
    rw [opa_ass, h1]
  · intro b
    apply Opa_Can_L (opa (i, b)) b x
    rw [← opa_ass, h2]

theorem Idempot_means_ida [GroupA G] (a : G) :
  a ⊹ a = a → a é a (⊹)-identidade :=
by
  intro h
  refine ⟨?_, ?_⟩
  · intro x
    have h1 : x ⊹ (a ⊹ a) = x ⊹ a := by
      exact data.univ (fun z => x ⊹ z) h
    rw [← opa_ass] at h1
    exact Opa_Can_R (x ⊹ a) x a h1
  · intro y
    have h1 : (a ⊹ a) ⊹ y = a ⊹ y := by
      exact data.univ (fun z => z ⊹ y) h
    rw [opa_ass] at h1
    exact Opa_Can_L (a ⊹ y) y a h1

theorem APass [GroupA G] :
  ∀ (a b : G), a = b → a ⊹ −b = z :=
by
  intro a b h
  have h1 :  a ⊹ −b = b ⊹ −b := by
    exact data.univ (· ⊹ −b) h
  rw [opa_ainv] at h1
  exact h1

theorem ABack [GroupA G] :
  ∀ (a b : G), a ⊹ −b = z → a = b :=
by
  intro a b h
  have h1 :  a ⊹ −b ⊹ b = z ⊹ b := by
    exact data.univ (· ⊹ b) h
  rw [id_opa, opa_ass, ainv_opa, opa_id] at h1
  exact h1

theorem Opa_Exists_Res_R [GroupA G] :
  ∀ (a b : G), ∃ (x : G), a ⊹ x = b :=
by
  intro a b
  refine ⟨(−a ⊹ b), ?_⟩
  rw [← opa_ass, opa_ainv, id_opa]

theorem Opa_Exists_Res_L [GroupA G] :
  ∀ (a b : G), ∃ (x : G), x ⊹ a = b :=
by
  intro a b
  refine ⟨(b ⊹ −a), ?_⟩
  rw [opa_ass, ainv_opa, opa_id]

theorem Opa_Only_Res_R [GroupA G] :
  ∀ (a u u' : G), a ⊹ u = b ∧ a ⊹ u' = b → u = u' :=
by
  intro a u u' h
  have h1 : a ⊹ u = a ⊹ u' := by
    rw [h.1, h.2]
  exact Opa_Can_L u u' a h1

theorem Opa_Only_Res_L [GroupA G] :
  ∀ (a u u' : G), u ⊹ a = b ∧ u' ⊹ a = b → u = u' :=
by
  intro a u u' h
  have h1 : u ⊹ a = u' ⊹ a := by
    rw [h.1, h.2]
  exact Opa_Can_R u u' a h1

theorem Cheap_Ida_L [GroupA G] :
  ∀ (a u : G), u ⊹ a = a → u = z :=
by
  intro a u h
  exact Opa_Only_Res_L a u z ⟨h, id_opa a⟩

theorem Cheap_Ida_R [GroupA G] :
  ∀ (u a : G), a ⊹ u = a → u = z :=
by
  intro u a h
  exact Opa_Only_Res_R a u z ⟨h, opa_id a⟩

theorem Cheap_Inva_L [GroupA G] :
  ∀ (a u : G), u ⊹ a = z → u = −a :=
by
  intro a u h
  exact Opa_Only_Res_L a u (−a) ⟨h, ainv_opa a⟩

theorem Cheap_Inva_R [GroupA G] :
  ∀ (a u : G), a ⊹ u = z → u = −a :=
by
  intro a u h
  exact Opa_Only_Res_R a u (−a) ⟨h, opa_ainv a⟩

theorem Inva_Inva [GroupA G] :
  ∀ (a : G), −(−a) = a :=
by
  intro a
  suffices h : −(−a) é o (⊹)-inverso de −a from Opa_Only_Res_L (−a) (−(−a)) a ⟨h.1, opa_ainv a⟩
  refine ⟨?_, ?_⟩
  · rw [ainv_opa]
  · rw [opa_ainv]

theorem Inva_Ida [GroupA G] :
  −z = (z : G) :=
by
  suffices h : −z é a (⊹)-identidade from Opa_Only_Id (−z) z ⟨h, ⟨opa_id, id_opa⟩⟩
  refine ⟨?_, ?_⟩
  · intro a
    rw [← opa_id a, opa_ass, opa_ainv]
  · intro b
    rw [← id_opa b, ← opa_ass, ainv_opa]

theorem Inva_Opa [GroupA G] :
  ∀ (a b : G), −(a ⊹ b) = −b ⊹ −a :=
by
  intro a b
  suffices h : (−b ⊹ −a) é o (⊹)-inverso de (a ⊹ b) from (Cheap_Inva_R (a ⊹ b) (−b ⊹ −a) h.2).symm
  refine ⟨?_, ?_⟩
  · rw [opa_ass, ← opa_ass (−a) a b, ainv_opa, id_opa, ainv_opa]
  · rw [opa_ass, ← opa_ass b (−b) (−a), opa_ainv, id_opa, opa_ainv]

theorem Not_Diff_CanA_L [GroupA G] :
  ¬ (∃ (i a b : G), a ≠ b ∧ i ⊹ a = i ⊹ b) :=
by
  intro ⟨i, a, b, h⟩
  suffices h' : a = b from h.1 h'
  exact Opa_Can_L a b i h.2

------------------------------------------------
-- PowA_Related Theorems :
------------------------------------------------

theorem Opa_Pow_Inv [GroupA G] :
  ∀ (a : G) (n : Nat), −(a ^ᴿ n) = −a ^ᴿ n :=
by
  intro a n
  suffices h : (−a ^ᴿ n) é o (⊹)-inverso de (a ^ᴿ n) from (Cheap_Inva_L (a ^ᴿ n) (−a ^ᴿ n) h.1).symm
  refine ⟨?_, ?_⟩
  · induction n with
    | zero => rw [PowA_R, PowA_R, opa_id]
    | succ k HI => rw [PowA_R, PowA_R, Opa_PowA_R, opa_ass,
                       ← opa_ass (−a) a (a ^ᴿ k), ainv_opa, id_opa, HI]
  · induction n with
    | zero => rw [PowA_R, PowA_R, opa_id]
    | succ k HI => rw [PowA_R, PowA_R, Opa_PowA_R, opa_ass,
                       ← opa_ass a (−a) (−a ^ᴿ k), opa_ainv, id_opa, HI]

notation:65 a:65 " ^ᴿ −" n:66 => (−a) ^ᴿ n
