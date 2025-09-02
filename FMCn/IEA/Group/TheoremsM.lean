import FMCn.IEA.Group.Definitions
import FMCn.IEA.Monoid.TheoremsM
import FMCn.CFR1.Useful

open MagmaM SemigroupM MonoidM GroupM

------------------------------------------------
-- GroupM Theorems (Easy/Basic) :
------------------------------------------------

theorem Opm_Can_R [GroupM G] :
  ∀ (a b c : G), a ⋆ c = b ⋆ c → a = b :=
by
  intro a b c h
  have h1 :  a ⋆ c ⋆ c⁻¹ = b ⋆ c ⋆ c⁻¹ := by
    exact data.univ (· ⋆ c⁻¹) h
  rw [opm_ass, opm_minv, opm_ass, opm_minv, opm_id, opm_id] at h1
  exact h1

theorem Opm_Can_L [GroupM G] :
  ∀ (a b c : G), c ⋆ a = c ⋆ b → a = b :=
by
  intro a b c h
  have h1 :  c⁻¹ ⋆ (c ⋆ a) = c⁻¹ ⋆ (c ⋆ b) := by
    exact data.univ (c⁻¹ ⋆ ·) h
  rw [← opm_ass, minv_opm, ← opm_ass, minv_opm, id_opm, id_opm] at h1
  exact h1

theorem Idm_Exists_for_all [GroupM G] (i : G):
  (∃ (x : G), i ⋆ x = x ∧ x ⋆ i = x) → i is_(⋆)-id :=
by
  intro h
  apply h.elim
  intro x ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · intro a
    apply Opm_Can_R (opm (a, i)) a x
    rw [opm_ass, h1]
  · intro b
    apply Opm_Can_L (opm (i, b)) b x
    rw [← opm_ass, h2]

theorem Idempot_means_idm [GroupM G] (a : G) :
  a ⋆ a = a → a is_(⋆)-id :=
by
  intro h
  refine ⟨?_, ?_⟩
  · intro x
    have h1 : x ⋆ (a ⋆ a) = x ⋆ a := by
      exact data.univ (fun z => x ⋆ z) h
    rw [← opm_ass] at h1
    exact Opm_Can_R (x ⋆ a) x a h1
  · intro y
    have h1 : (a ⋆ a) ⋆ y = a ⋆ y := by
      exact data.univ (fun z => z ⋆ y) h
    rw [opm_ass] at h1
    exact Opm_Can_L (a ⋆ y) y a h1

theorem MPass [GroupM G] :
  ∀ (a b : G), a = b → a ⋆ b⁻¹ = e :=
by
  intro a b h
  have h1 :  a ⋆ b⁻¹ = b ⋆ b⁻¹ := by
    exact data.univ (· ⋆ b⁻¹) h
  rw [opm_minv] at h1
  exact h1

theorem MBack [GroupM G] :
  ∀ (a b : G), a ⋆ b⁻¹ = e → a = b :=
by
  intro a b h
  have h1 :  a ⋆ b⁻¹ ⋆ b = e ⋆ b := by
    exact data.univ (· ⋆ b) h
  rw [id_opm, opm_ass, minv_opm, opm_id] at h1
  exact h1

theorem Opm_Exists_Res_R [GroupM G] :
  ∀ (a b : G), ∃ (x : G), a ⋆ x = b :=
by
  intro a b
  refine ⟨(a⁻¹ ⋆ b), ?_⟩
  rw [← opm_ass, opm_minv, id_opm]

theorem Opm_Exists_Res_L [GroupM G] :
  ∀ (a b : G), ∃ (x : G), x ⋆ a = b :=
by
  intro a b
  refine ⟨(b ⋆ a⁻¹), ?_⟩
  rw [opm_ass, minv_opm, opm_id]

theorem Opm_Only_Res_R [GroupM G] :
  ∀ (a u u' : G), a ⋆ u = b ∧ a ⋆ u' = b → u = u' :=
by
  intro a u u' h
  have h1 : a ⋆ u = a ⋆ u' := by
    rw [h.1, h.2]
  exact Opm_Can_L u u' a h1

theorem Opm_Only_Res_L [GroupM G] :
  ∀ (a u u' : G), u ⋆ a = b ∧ u' ⋆ a = b → u = u' :=
by
  intro a u u' h
  have h1 : u ⋆ a = u' ⋆ a := by
    rw [h.1, h.2]
  exact Opm_Can_R u u' a h1

theorem Cheap_Idm_L [GroupM G] :
  ∀ (a u : G), u ⋆ a = a → u = e :=
by
  intro a u h
  exact Opm_Only_Res_L a u e ⟨h, id_opm a⟩

theorem Cheap_Idm_R [GroupM G] :
  ∀ (u a : G), a ⋆ u = a → u = e :=
by
  intro u a h
  exact Opm_Only_Res_R a u e ⟨h, opm_id a⟩

theorem Cheap_Invm_L [GroupM G] :
  ∀ (a u : G), u ⋆ a = e → u = a⁻¹ :=
by
  intro a u h
  exact Opm_Only_Res_L a u a⁻¹ ⟨h, minv_opm a⟩

theorem Cheap_Invm_R [GroupM G] :
  ∀ (a u : G), a ⋆ u = e → u = a⁻¹ :=
by
  intro a u h
  exact Opm_Only_Res_R a u a⁻¹ ⟨h, opm_minv a⟩

theorem Invm_Invm [GroupM G] :
  ∀ (a : G), (a⁻¹)⁻¹ = a :=
by
  intro a
  suffices h : (a⁻¹)⁻¹ is_(⋆)-invOf a⁻¹ from Opm_Only_Res_L a⁻¹ (a⁻¹)⁻¹ a ⟨h.1, opm_minv a⟩
  refine ⟨?_, ?_⟩
  · rw [minv_opm]
  · rw [opm_minv]

theorem Invm_Idm [GroupM G] :
  e⁻¹ = (e : G) :=
by
  suffices h : e⁻¹ is_(⋆)-id from Opm_Only_Id e⁻¹ e ⟨h, ⟨opm_id, id_opm⟩⟩
  refine ⟨?_, ?_⟩
  · intro a
    rw [← opm_id a, opm_ass, opm_minv]
  · intro b
    rw [← id_opm b, ← opm_ass, minv_opm]

theorem Invm_Opm [GroupM G] :
  ∀ (a b : G), (a ⋆ b)⁻¹ = b⁻¹ ⋆ a⁻¹ :=
by
  intro a b
  suffices h : (b⁻¹ ⋆ a⁻¹) is_(⋆)-invOf (a ⋆ b) from (Cheap_Invm_R (a ⋆ b) (b⁻¹ ⋆ a⁻¹) h.2).symm
  refine ⟨?_, ?_⟩
  · rw [opm_ass, ← opm_ass a⁻¹ a b, minv_opm, id_opm, minv_opm]
  · rw [opm_ass, ← opm_ass b b⁻¹ a⁻¹, opm_minv, id_opm, opm_minv]

theorem Not_Diff_CanM_L [GroupM G] :
  ¬ (∃ (i a b : G), a ≠ b ∧ i ⋆ a = i ⋆ b) :=
by
  intro ⟨i, a, b, h⟩
  suffices h' : a = b from h.1 h'
  exact Opm_Can_L a b i h.2

------------------------------------------------
-- PowM_Related Theorems :
------------------------------------------------

theorem Opm_Pow_Inv [GroupM G] :
  ∀ (a : G) (n : Nat), (a ↑ᴿ n)⁻¹ = a⁻¹ ↑ᴿ n :=
by
  intro a n
  suffices h : (a⁻¹ ↑ᴿ n) is_(⋆)-invOf (a ↑ᴿ n) from (Cheap_Invm_L (a ↑ᴿ n) (a⁻¹ ↑ᴿ n) h.1).symm
  refine ⟨?_, ?_⟩
  · induction n with
    | zero => rw [PowM_R, PowM_R, opm_id]
    | succ k HI => rw [PowM_R, PowM_R, Opm_PowM_R, opm_ass,
                       ← opm_ass a⁻¹ a (a ↑ᴿ k), minv_opm, id_opm, HI]
  · induction n with
    | zero => rw [PowM_R, PowM_R, opm_id]
    | succ k HI => rw [PowM_R, PowM_R, Opm_PowM_R, opm_ass,
                       ← opm_ass a a⁻¹ (a⁻¹ ↑ᴿ k), opm_minv, id_opm, HI]

notation:65 a:65 " ↑ᴿ-" n:66 => (a⁻¹) ↑ᴿ n

------------------------------------------------
-- SubGroupMs :
------------------------------------------------

/-class SubGroupM [GroupM G] (S : Set G) : Prop :=
  Opm_in : ∀ (a b : G), a ∈ S ∧ b ∈ S → (a ⋆ b) ∈ S
  Id_in : (e : G) ∈ S
  Inv_in : ∀ (a : G), a ∈ S → (a⁻¹) ∈ S

GroupM.lean:284:35
Expected type
G : Type ?u.89434
inst✝ : GroupM G
⊢ Type ?u.89434
Messages (1)
GroupM.lean:284:30
type expected, got
  (set G : ?m.89440 PUnit)
All Messages (1)
-/
