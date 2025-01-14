import FMCn.IEA.Group.Definitions
import FMCn.IEA.Monoid.Theorems

open Magma Semigroup Monoid Group

------------------------------------------------
-- Useful Theorems :
------------------------------------------------
theorem determinist_fun {α β : Type u} :
  ∀ (f : α → β) (a a' : α), a = a' → f a = f a' :=
by
  intro f a a' h
  rw [h]

------------------------------------------------
-- Group Theorems (Easy/Basic) :
------------------------------------------------

theorem Op_Can_R [Group G] :
  ∀ (a b c : G), a ⋆ c = b ⋆ c → a = b :=
by
  intro a b c h
  have h1 :  a ⋆ c ⋆ c⁻¹ = b ⋆ c ⋆ c⁻¹ := by
    exact determinist_fun (· ⋆ c⁻¹) (a ⋆ c) (b ⋆ c) h
  rw [Op_Ass, Op_Inv_R, Op_Ass, Op_Inv_R, Op_Id, Op_Id] at h1
  exact h1

theorem Op_Can_L [Group G] :
  ∀ (a b c : G), c ⋆ a = c ⋆ b → a = b :=
by
  intro a b c h
  have h1 :  c⁻¹ ⋆ (c ⋆ a) = c⁻¹ ⋆ (c ⋆ b) := by
    exact determinist_fun (c⁻¹ ⋆ ·) (c ⋆ a) (c ⋆ b) h
  rw [← Op_Ass, Op_Inv_L, ← Op_Ass, Op_Inv_L, Id_Op, Id_Op] at h1
  exact h1

theorem Id_Exists_for_all [Group G] (i : G):
  (∃ (x : G), i ⋆ x = x ∧ x ⋆ i = x) → i é a identidade :=
by
  intro h
  apply h.elim
  intro x ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · intro a
    apply Op_Can_R (op (a, i)) a x
    rw [Op_Ass, h1]
  · intro b
    apply Op_Can_L (op (i, b)) b x
    rw [← Op_Ass, h2]

theorem Idempot_means_id [Group G] (a : G) :
  a ⋆ a = a → a é a identidade :=
by
  intro h
  refine ⟨?_, ?_⟩
  · intro x
    have h1 : x ⋆ (a ⋆ a) = x ⋆ a := by
      exact determinist_fun (fun z => x ⋆ z) (a ⋆ a) a h
    rw [← Op_Ass] at h1
    exact Op_Can_R (x ⋆ a) x a h1
  · intro y
    have h1 : (a ⋆ a) ⋆ y = a ⋆ y := by
      exact determinist_fun (fun z => z ⋆ y) (a ⋆ a) a h
    rw [Op_Ass] at h1
    exact Op_Can_L (a ⋆ y) y a h1

theorem Pass [Group G] :
  ∀ (a b : G), a = b → a ⋆ b⁻¹ = e :=
by
  intro a b h
  have h1 :  a ⋆ b⁻¹ = b ⋆ b⁻¹ := by
    exact determinist_fun (· ⋆ b⁻¹) a b h
  rw [Op_Inv_R] at h1
  exact h1

theorem Back [Group G] :
  ∀ (a b : G), a ⋆ b⁻¹ = e → a = b :=
by
  intro a b h
  have h1 :  a ⋆ b⁻¹ ⋆ b = e ⋆ b := by
    exact determinist_fun (· ⋆ b) (a ⋆ b⁻¹) e h
  rw [Id_Op, Op_Ass, Op_Inv_L, Op_Id] at h1
  exact h1

theorem Op_Exists_Res_R [Group G] :
  ∀ (a b : G), ∃ (x : G), a ⋆ x = b :=
by
  intro a b
  refine ⟨(a⁻¹ ⋆ b), ?_⟩
  rw [← Op_Ass, Op_Inv_R, Id_Op]

theorem Op_Exists_Res_L [Group G] :
  ∀ (a b : G), ∃ (x : G), x ⋆ a = b :=
by
  intro a b
  refine ⟨(b ⋆ a⁻¹), ?_⟩
  rw [Op_Ass, Op_Inv_L, Op_Id]

theorem Op_Only_Res_R [Group G] :
  ∀ (a u u' : G), a ⋆ u = b ∧ a ⋆ u' = b → u = u' :=
by
  intro a u u' h
  have h1 : a ⋆ u = a ⋆ u' := by
    rw [h.1, h.2]
  exact Op_Can_L u u' a h1

theorem Op_Only_Res_L [Group G] :
  ∀ (a u u' : G), u ⋆ a = b ∧ u' ⋆ a = b → u = u' :=
by
  intro a u u' h
  have h1 : u ⋆ a = u' ⋆ a := by
    rw [h.1, h.2]
  exact Op_Can_R u u' a h1

theorem Cheap_Id_L [Group G] :
  ∀ (a u : G), u ⋆ a = a → u = e :=
by
  intro a u h
  exact Op_Only_Res_L a u e ⟨h, Id_Op a⟩

theorem Cheap_Id_R [Group G] :
  ∀ (u a : G), a ⋆ u = a → u = e :=
by
  intro u a h
  exact Op_Only_Res_R a u e ⟨h, Op_Id a⟩

theorem Cheap_Inv_L [Group G] :
  ∀ (a u : G), u ⋆ a = e → u = a⁻¹ :=
by
  intro a u h
  exact Op_Only_Res_L a u a⁻¹ ⟨h, Op_Inv_L a⟩

theorem Cheap_Inv_R [Group G] :
  ∀ (a u : G), a ⋆ u = e → u = a⁻¹ :=
by
  intro a u h
  exact Op_Only_Res_R a u a⁻¹ ⟨h, Op_Inv_R a⟩

theorem Inv_Inv [Group G] :
  ∀ (a : G), (a⁻¹)⁻¹ = a :=
by
  intro a
  suffices h : (a⁻¹)⁻¹ é o inverso de a⁻¹ from Op_Only_Res_L a⁻¹ (a⁻¹)⁻¹ a ⟨h.1, Op_Inv_R a⟩
  refine ⟨?_, ?_⟩
  · rw [Op_Inv_L]
  · rw [Op_Inv_R]

theorem Inv_Id [Group G] :
  e⁻¹ = (e : G) :=
by
  suffices h : e⁻¹ é a identidade from Op_Only_Id e⁻¹ e ⟨h, ⟨Op_Id, Id_Op⟩⟩
  refine ⟨?_, ?_⟩
  · intro a
    rw [← Op_Id a, Op_Ass, Op_Inv_R]
  · intro b
    rw [← Id_Op b, ← Op_Ass, Op_Inv_L]

theorem Inv_Op [Group G] :
  ∀ (a b : G), (a ⋆ b)⁻¹ = b⁻¹ ⋆ a⁻¹ :=
by
  intro a b
  suffices h : (b⁻¹ ⋆ a⁻¹) é o inverso de (a ⋆ b) from (Cheap_Inv_R (a ⋆ b) (b⁻¹ ⋆ a⁻¹) h.2).symm
  refine ⟨?_, ?_⟩
  · rw [Op_Ass, ← Op_Ass a⁻¹ a b, Op_Inv_L, Id_Op, Op_Inv_L]
  · rw [Op_Ass, ← Op_Ass b b⁻¹ a⁻¹, Op_Inv_R, Id_Op, Op_Inv_R]

theorem Not_Diff_Can_L [Group G] :
  ¬ (∃ (i a b : G), a ≠ b ∧ i ⋆ a = i ⋆ b) :=
by
  intro ⟨i, a, b, h⟩
  suffices h' : a = b from h.1 h'
  exact Op_Can_L a b i h.2

------------------------------------------------
-- Pow_Related Theorems :
------------------------------------------------

theorem Op_Pow_Inv [Group G] :
  ∀ (a : G) (n : Nat), (a ↑ᴿ n)⁻¹ = a⁻¹ ↑ᴿ n :=
by
  intro a n
  suffices h : (a⁻¹ ↑ᴿ n) é o inverso de (a ↑ᴿ n) from (Cheap_Inv_L (a ↑ᴿ n) (a⁻¹ ↑ᴿ n) h.1).symm
  refine ⟨?_, ?_⟩
  · induction n with
    | zero => rw [Pow_R, Pow_R, Op_Id]
    | succ k HI => rw [Pow_R, Pow_R, Op_Pow_R, Op_Ass,
                       ← Op_Ass a⁻¹ a (a ↑ᴿ k), Op_Inv_L, Id_Op, HI]
  · induction n with
    | zero => rw [Pow_R, Pow_R, Op_Id]
    | succ k HI => rw [Pow_R, Pow_R, Op_Pow_R, Op_Ass,
                       ← Op_Ass a a⁻¹ (a⁻¹ ↑ᴿ k), Op_Inv_R, Id_Op, HI]

notation:65 a:65 " ↑ᴿ -" n:66 => (a⁻¹) ↑ᴿ n

------------------------------------------------
-- Subgroups :
------------------------------------------------

/-class Subgroup [Group G] (S : Set G) : Prop :=
  Op_in : ∀ (a b : G), a ∈ S ∧ b ∈ S → (a ⋆ b) ∈ S
  Id_in : (e : G) ∈ S
  Inv_in : ∀ (a : G), a ∈ S → (a⁻¹) ∈ S

Group.lean:284:35
Expected type
G : Type ?u.89434
inst✝ : Group G
⊢ Type ?u.89434
Messages (1)
Group.lean:284:30
type expected, got
  (set G : ?m.89440 PUnit)
All Messages (1)
-/
