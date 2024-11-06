import Init.Prelude
import FMCn.CFR1.Definitions
import FMCn.CFR1.Useful
import FMCn.CFR1.Functions

------------------------------------------------
-- Parte Relação de Equivalência:
------------------------------------------------

theorem iso_refl:
  reflexive iso :=
by
  intro α
  refine ⟨id, id, ?_, ?_⟩
  · rw [(id_comp id).1]
  · rw [(id_comp id).1]

theorem iso_symm:
  symmetric iso :=
by
  intro α β ⟨f, g, h⟩
  refine ⟨g, f, h.2, h.1⟩

theorem iso_trans:
  transitive iso :=
by
  intro α β γ ⟨f, g, h⟩ ⟨f', g', h'⟩
  refine ⟨(f' ⋄ f), (g ⋄ g'), ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc g' g f,
        h.1, (id_comp g').1, h'.1]
  · rw [comp_assoc, ← comp_assoc f f' g',
        h'.2, (id_comp f).1, h.2]

theorem iso_eq_rel:
  equivalent_relation iso :=
by
  refine ⟨iso_refl, iso_symm, iso_trans⟩

------------------------------------------------
-- Parte Estrutura Algébrica:
------------------------------------------------

theorem iso_empty:
  respects_empty :=
by
  exact iso_refl Empty

theorem iso_unit:
  respects_unit :=
by
  exact iso_refl Unit

theorem iso_sum:
  respects_sum :=
by
  intro α α' β β' ⟨⟨fa, fa', ha⟩,⟨gb, gb', hb⟩⟩
  refine ⟨Fun_to_sum fa gb, Fun_to_sum fa' gb', ?_, ?_⟩
  · funext ab'
    rw [comp_def]
    unfold Fun_to_sum
    cases ab' with
    | inl a' => simp; rw [← comp_def fa' fa, ha.1, id]
    | inr b' => simp; rw [← comp_def gb' gb, hb.1, id]
  · funext ab
    rw [comp_def]
    unfold Fun_to_sum
    cases ab with
    | inl a => simp; rw [← comp_def fa fa', ha.2, id]
    | inr b => simp; rw [← comp_def gb gb', hb.2, id]

theorem iso_prod:
  respects_prod :=
by
  intro α α' β β' ⟨⟨fa, fa', ha⟩, ⟨gb, gb', hb⟩⟩
  refine ⟨Fun_to_cross fa gb, Fun_to_cross fa' gb', ?_, ?_⟩
  · funext w'
    rw [comp_def]
    unfold Fun_to_cross
    simp
    rw [← comp_def fa' fa, ← comp_def gb' gb,
        ha.1, hb.1, id, id]
  · funext w
    rw [comp_def]
    unfold Fun_to_cross
    simp
    rw [← comp_def fa fa', ← comp_def gb gb',
        ha.2, hb.2, id, id]

theorem iso_fun:
  respects_fun :=
by
  intro α α' β β' ⟨⟨fa, fa', ha⟩, ⟨gb, gb', hb⟩⟩
  refine ⟨Fun_to_fun fa' gb, Fun_to_fun fa gb', ?_, ?_⟩
  · funext h
    rw [comp_def]
    unfold Fun_to_fun
    simp
    rw [comp_assoc fa' (h ⋄ fa) gb', comp_assoc fa' fa h,
        ha.1, (id_comp h).2, ← comp_assoc h gb' gb,
        hb.1, (id_comp h).1]
  · funext h
    rw [comp_def]
    unfold Fun_to_fun
    simp
    rw [comp_assoc fa (h ⋄ fa') gb, comp_assoc fa fa' h,
        ha.2, (id_comp h).2, ← comp_assoc h gb gb',
        hb.2, (id_comp h).1]

theorem iso_algebric_structure:
  respects_algebric_structure :=
by
  refine ⟨iso_empty, iso_unit, iso_sum, iso_prod, iso_fun⟩

------------------------------------------------
-- Congruência:
------------------------------------------------

theorem iso_congruent:
  congruent :=
by
  refine ⟨iso_eq_rel, iso_algebric_structure⟩

------------------------------------------------
-- Teoremas Divertidos
------------------------------------------------

------------------------Sum-Pow------------------------

theorem iso_pow_sum {α β δ : Type}:
  (α ⊕ β → δ) ≅ ((α → δ) × (β → δ)) :=
by
  refine ⟨Pow_Sum_to_Prod, Prod_Pow_to_Sum, ?_, ?_⟩
  · funext w
    rw [comp_def, Prod_Pow_to_Sum, Pow_Sum_to_Prod, id]
  · funext f
    rw [comp_def, Pow_Sum_to_Prod, Prod_Pow_to_Sum, id]
    simp
    funext x
    cases x with
    | inl a => rfl
    | inr b => rfl

------------------------Curry------------------------

theorem iso_curry {α β δ : Type}:
  (α → β → δ) ≅ (α × β → δ) :=
by
  refine ⟨uncurry, curry, ?_, ?_⟩
  · funext f w
    rw [comp_def, curry, uncurry, id]
  · funext g a b
    rw [comp_def, uncurry, curry, id]

-----------------------Pow-Empty-----------------------
/-
def Pow_empty {α : Type}: (Empty → α) → Unit
  | _ => ()

def Empty_fun {α : Type} : Empty → α

def Unit_to_pow {α : Type}: Unit → Empty → α
  | _ => Empty_fun

theorem only_one_empty_fun {α : Type}:
  ∀ (g g' : Empty → α), g = g' :=
by
  intro g g'
  funext a
  contradiction

theorem iso_eq_one {α : Type} :
  (Empty → α) ≅ Unit :=
by
  refine ⟨Pow_empty, Unit_to_pow, ?_, ?_⟩
  · funext ()
    rw [comp_def, Unit_to_pow, Pow_empty, id]
  · funext f
    rw [comp_def, Pow_empty, Unit_to_pow, id]
    simp
    exact only_one_empty_fun Empty_fun f
-/
------------------------Pow-One------------------------

theorem iso_pow_unit {α : Type}:
  (Unit → α) ≅ α :=
by
  refine ⟨Pow_one, Pow_one_back, ?_, ?_⟩
  · funext a
    rw [comp_def, Pow_one_back, Pow_one, id]
  · funext f
    rw [comp_def, Pow_one, Pow_one_back, id]

------------------------Pow-Two------------------------

theorem iso_pow_two {α : Type}:
  (Unit ⊕ Unit → α) ≅ (α × α) :=
by
  refine ⟨Pow_two, Two_pow, ?_, ?_⟩
  · funext w
    rw [comp_def, Two_pow, Pow_two, id]
  · funext f x
    rw [comp_def, Pow_two, Two_pow, id]
    cases x with
    | inl _ => rfl
    | inr _ => rfl

------------------------Unit-Pow------------------------

theorem iso_one_pow {α : Type}:
  (α → Unit) ≅ Unit :=
by
  refine ⟨One_pow, One_pow_back, ?_, ?_⟩
  · funext ()
    rw [comp_def, One_pow_back, One_pow, id]
  · funext f
    rw [comp_def, One_pow, One_pow_back, id]

-----------------------Empty-Pow-----------------------

/-theorem iso_empty_pow {α : Type}:
  (α → Empty) ≅ Empty :=
by
-/

--------------------Empty-Pow-Empty--------------------
/--/
theorem iso_empty_pow_empty:
  (Empty → Empty) ≅ Unit :=
by
  exact iso_eq_one
-/
------------------------Distr-L------------------------

theorem iso_distr_L {α β δ : Type}:
  (δ × (α ⊕ β)) ≅ ((δ × α) ⊕ (δ × β)) :=
by
  refine ⟨Distr α β δ, Distr_back, ?_, ?_⟩
  · funext x
    rw [comp_def, Distr_back, Distr, id]
    cases x with
    | inl da => rfl
    | inr db => rfl
  · funext ⟨d, x⟩
    rw [comp_def, Distr, Distr_back, id]
    cases x with
    | inl a => rfl
    | inr b => rfl

------------------------Sum-Ass------------------------

theorem iso_sum_ass {α β γ : Type}:
  (α ⊕ β ⊕ γ) ≅ ((α ⊕ β) ⊕ γ) :=
by
  refine ⟨Ass_sum_one, Ass_sum_two, ?_, ?_⟩
  · funext x
    rw [comp_def, Ass_sum_two, Ass_sum_one, id]
    cases x with
    | inl ab => cases ab with
                | inl a => rfl
                | inr b => rfl
    | inr c => rfl
  · funext y
    rw [comp_def, Ass_sum_one, Ass_sum_two, id]
    cases y with
    | inl a => rfl
    | inr bc => cases bc with
                | inl b => rfl
                | inr c => rfl

------------------------Sum-Com------------------------

theorem iso_sum_com {α β : Type}:
  (α ⊕ β) ≅ (β ⊕ α) :=
by
  refine ⟨Com_sum α β, Com_sum β α, ?_, ?_⟩
  · funext x
    rw [comp_def, Com_sum, Com_sum, id]
    cases x with
    | inr a => rfl
    | inl b => rfl
  · funext y
    rw [comp_def, Com_sum, Com_sum, id]
    cases y with
    | inr b => rfl
    | inl a => rfl

-------------------------Sum-Id-------------------------

theorem iso_sum_id {α : Type}:
  (α ⊕ Empty) ≅ α :=
by
  refine ⟨Id_sum, Sum_id, ?_, ?_⟩
  · funext a
    rw [comp_def, Sum_id, Id_sum, id]
  · funext x
    rw [comp_def, Id_sum, Sum_id, id]
    cases x with
    | inl a => rfl
    | inr e => contradiction

------------------------Prod-Ass------------------------

theorem iso_prod_ass {α β γ : Type}:
  ((α × β) × γ) ≅ (α × β × γ) :=
by
  refine ⟨Ass_prod_one, Ass_prod_two, ?_, ?_⟩
  · funext ⟨a, bc⟩
    rw [comp_def, Ass_prod_two, Ass_prod_one, id]
  · funext ⟨ab, c⟩
    rw [comp_def, Ass_prod_two, Ass_prod_one, id]

------------------------Prod-Com------------------------

theorem iso_prod_com {α β : Type}:
  (α × β) ≅ (β × α) :=
by
  refine ⟨Com_prod α β, Com_prod β α, ?_, ?_⟩
  · funext w
    rw [comp_def, Com_prod, Com_prod, id]
  · funext w'
    rw [comp_def, Com_prod, Com_prod, id]

------------------------Distr-R------------------------

theorem iso_distr_R {α β δ : Type}:
  ((α ⊕ β) × δ) ≅ (α × δ ⊕ β × δ) :=
by

  have h : ((α ⊕ β) × δ) ≅ (δ × (α ⊕ β)) :=
  by
    exact iso_prod_com
  have h1 : (δ × (α ⊕ β)) ≅ (δ × α ⊕ δ × β) :=
  by
    exact iso_distr_L
  have h2 : (δ × α ⊕ δ × β) ≅ (α × δ ⊕ β × δ) :=
  by
    have h': (δ × α) ≅ (α × δ) :=
    by
      exact iso_prod_com
    have h'': (δ × β) ≅ (β × δ) :=
    by
      exact iso_prod_com
    exact iso_sum (δ × α) (α × δ) (δ × β) (β × δ) ⟨h', h''⟩
  have h3 : (δ × (α ⊕ β)) ≅ (α × δ ⊕ β × δ) :=
  by
    exact iso_trans (δ × (α ⊕ β)) (δ × α ⊕ δ × β) (α × δ ⊕ β × δ) h1 h2
  exact iso_trans ((α ⊕ β) × δ) (δ × (α ⊕ β)) (α × δ ⊕ β × δ) h h3

-------------------------Prod-Id-------------------------

theorem iso_prod_id {α : Type}:
  (α × Unit) ≅ α :=
by
  refine ⟨Id_prod, Prod_id, ?_, ?_⟩
  · funext a
    rw [comp_def, Prod_id, Id_prod, id]
  · funext w
    rw [comp_def, Id_prod, Prod_id, id]

------------------------Prod-Anul------------------------

/-
def to_empty {α : Type}: α × Empty → Empty
  | w => w.2

def from_empty {α : Type}: Empty → α × Empty
  | x => ⟨Empty_fun x, x⟩

theorem iso_prod_anul {a : Type}:
  (α × Empty) ≅ Empty :=
by
  refine ⟨to_empty, from_empty, ?_, ?_⟩
  · funext x
    rw [comp_def, from_empty, to_empty, id]
  · funext x
    rw [comp_def, from_empty, to_empty, id]
    simp
    -/

-----------------------Pow-Two-Sum-----------------------
/-
theorem iso_pow_two_sum {α β : Type}:
  (Unit ⊕ Unit → α ⊕ β) ≅ (α × α ⊕ α × β ⊕ β × α ⊕ β × β) :=
by
  have h1: (Unit ⊕ Unit → α ⊕ β) ≅ ((α ⊕ β) × (α ⊕ β)) :=
  by
    exact iso_pow_two
  have h2: ((α ⊕ β) × (α ⊕ β)) ≅ ((α ⊕ β) × α ⊕ (α ⊕ β) × β) :=
  by
    exact iso_distr_L
  have h3: ((α ⊕ β) × α ⊕ (α ⊕ β) × β) ≅ (α × (α ⊕ β) ⊕ β × (α ⊕ β)) :=
  by
    have h': ((α ⊕ β) × α) ≅ (α × (α ⊕ β)) :=
    by
      exact iso_prod_com
    have h'': ((α ⊕ β) × β) ≅ (β × (α ⊕ β)) :=
    by
      exact iso_prod_com
    exact iso_sum ((α ⊕ β) × α) (α × (α ⊕ β)) ((α ⊕ β) × β) (β × (α ⊕ β)) ⟨h',h''⟩
  have h4: (α × (α ⊕ β) ⊕ β × (α ⊕ β)) ≅ (α × α ⊕ α × β ⊕ β × α ⊕ β × β) :=
  by
    have h': (α × (α ⊕ β)) ≅ (α × α ⊕ α × β) :=
    by
      exact iso_distr_L
    have h'': (β × (α ⊕ β)) ≅ (β × α ⊕ β × β) :=
    by
      exact iso_distr_L
    have h''': (α × (α ⊕ β) ⊕ β × (α ⊕ β)) ≅ ((α × α ⊕ α × β) ⊕ β × α ⊕ β × β) := by
      exact iso_sum (α × (α ⊕ β)) (α × α ⊕ α × β) (β × (α ⊕ β)) (β × α ⊕ β × β) ⟨h', h''⟩
    sorry
  apply iso_trans (α × (α ⊕ β) ⊕ β × (α ⊕ β))
-/
