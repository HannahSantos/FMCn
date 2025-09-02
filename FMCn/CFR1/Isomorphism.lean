import FMCn.CFR1.Definitions
import FMCn.CFR1.Useful
import FMCn.CFR1.Functions

namespace data
------------------------------------------------
-- Parte Relação de Equivalência:
------------------------------------------------

theorem iso_refl:
  (≅) is_refl :=
by
  intro α
  refine ⟨id, id, ?_, ?_⟩
  · rw [(id_comp id).1]
  · rw [(id_comp id).1]

theorem iso_symm:
  (≅) is_symm :=
by
  intro α β ⟨f, g, h⟩
  refine ⟨g, f, h.2, h.1⟩

theorem iso_trans:
  (≅) is_trans :=
by
  intro α β γ ⟨f, g, h⟩ ⟨f', g', h'⟩
  refine ⟨(f' ⋄ f), (g ⋄ g'), ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc g' g f,
        h.1, (id_comp g').1, h'.1]
  · rw [comp_assoc, ← comp_assoc f f' g',
        h'.2, (id_comp f).1, h.2]

instance : Trans iso iso iso where
  trans := by apply iso_trans

theorem iso_eq_rel:
  (≅) is_equivRel :=
by
  refine ⟨iso_refl, iso_symm, iso_trans⟩

------------------------------------------------
-- Parte Estrutura Algébrica:
------------------------------------------------

theorem iso_empty:
  (≅)-resp𝟘 :=
by
  exact iso_refl Empty

theorem iso_unit:
  (≅)-resp𝟙 :=
by
  exact iso_refl Unit

theorem iso_sum:
  (≅)-resp(⊕) :=
by
  intro α α' β β' ⟨⟨fa, fa', ha⟩, ⟨gb, gb', hb⟩⟩
  refine ⟨fa ⊕ gb, fa' ⊕ gb', ?_, ?_⟩
  · funext ab'
    rw [comp_def]
    cases ab' with
    | inl a' => rw [copairing_left, copairing_left,
                    ← comp_def fa' fa, ha.1, id_def,
                    id_def]
    | inr b' => rw [copairing_right, copairing_right,
                    ← comp_def gb' gb, hb.1, id_def,
                    id_def]
  · funext ab
    rw [comp_def]
    cases ab with
    | inl a => rw [copairing_left, copairing_left,
                   ← comp_def fa fa', ha.2, id_def,
                   id_def]
    | inr b => rw [copairing_right, copairing_right,
                   ← comp_def gb gb', hb.2, id_def,
                   id_def]

theorem iso_prod:
  (≅)-resp(×) :=
by
  intro α α' β β' ⟨⟨fa, fa', ha⟩, ⟨gb, gb', hb⟩⟩
  refine ⟨fa × gb, fa' × gb', ?_, ?_⟩
  · funext w'
    rw [comp_def, prod_fun_def, prod_fun_def,
        ← comp_def fa' fa, ← comp_def gb' gb,
        ha.1, hb.1, id_def, id_def, id_def]
  · funext w
    rw [comp_def, prod_fun_def, prod_fun_def,
        ← comp_def fa fa', ← comp_def gb gb',
        ha.2, hb.2, id_def, id_def, id_def]

theorem iso_fun:
  (≅)-resp(→) :=
by
  intro α α' β β' ⟨⟨fa, fa', ha⟩, ⟨gb, gb', hb⟩⟩
  refine ⟨Fun_to_fun fa' gb, Fun_to_fun fa gb', ?_, ?_⟩
  · funext h
    rw [comp_def, Fun_to_fun_def, Fun_to_fun_def]
    rw [comp_assoc fa' (h ⋄ fa) gb', comp_assoc fa' fa h,
        ha.1, (id_comp h).2, ← comp_assoc h gb' gb,
        hb.1, (id_comp h).1, id_def]
  · funext h
    rw [comp_def, Fun_to_fun_def, Fun_to_fun_def]
    rw [comp_assoc fa (h ⋄ fa') gb, comp_assoc fa fa' h,
        ha.2, (id_comp h).2, ← comp_assoc h gb gb',
        hb.2, (id_comp h).1, id_def]

theorem iso_algebric_structure:
  (≅)-respAlgebStruct :=
by
  refine ⟨iso_empty, iso_unit, iso_sum, iso_prod, iso_fun⟩

------------------------------------------------
-- Congruência:
------------------------------------------------

theorem iso_congruent:
  (≅)-isCongr :=
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
    rw [comp_def, Prod_Pow_to_Sum, Pow_Sum_to_Prod, id_def]
  · funext f
    rw [comp_def, Pow_Sum_to_Prod, Prod_Pow_to_Sum, id_def]
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
    rw [comp_def, curry, uncurry, id_def]
  · funext g a b
    rw [comp_def, uncurry, curry, id_def]

-----------------------Pow-Empty-----------------------

theorem only_one_empty_fun {α : Type}:
  ∀ (g g' : 𝟘 → α), g = g' :=
by
  intro g g'
  funext a
  contradiction

theorem iso_eq_one {α : Type} :
  (𝟘 → α) ≅ 𝟙 :=
by
  refine ⟨Pow_empty, Unit_to_pow, ?_, ?_⟩
  · funext ()
    rw [comp_def, Unit_to_pow, Pow_empty, id_def]
  · funext f
    rw [comp_def, Pow_empty, Unit_to_pow, id_def]
    exact only_one_empty_fun fromEmpty f

------------------------Pow-One------------------------

theorem iso_pow_unit {α : Type}:
  (𝟙 → α) ≅ α :=
by
  refine ⟨Pow_one, Pow_one_back, ?_, ?_⟩
  · funext a
    rw [comp_def, Pow_one_back, Pow_one, id_def]
  · funext f
    rw [comp_def, Pow_one, Pow_one_back, id_def]

------------------------Pow-Two------------------------

theorem iso_pow_two {α : Type}:
  (𝟚 → α) ≅ (α × α) :=
by
  refine ⟨Pow_two, Two_pow, ?_, ?_⟩
  · funext w
    rw [comp_def, Two_pow, Pow_two, id_def]
  · funext f x
    rw [comp_def, Pow_two, Two_pow, id_def]
    cases x with
    | inl _ => rfl
    | inr _ => rfl

------------------------Unit-Pow------------------------

theorem iso_one_pow {α : Type}:
  (α → 𝟙) ≅ 𝟙 :=
by
  refine ⟨One_pow, One_pow_back, ?_, ?_⟩
  · funext ()
    rw [comp_def, One_pow_back, One_pow, id_def]
  · funext f
    rw [comp_def, One_pow, One_pow_back, id_def]

-----------------------Empty-Pow-----------------------
/-
theorem iso_empty_pow {α : Type}:
  (α → 𝟘) ≅ 𝟘 :=
by
  sorry
-/
--------------------Empty-Pow-Empty--------------------

theorem iso_empty_pow_empty:
  (𝟘 → 𝟘) ≅ 𝟙 :=
by
  exact iso_eq_one

------------------------Distr-L------------------------

theorem iso_distr_L {α β δ : Type}:
  (δ × (α ⊕ β)) ≅ ((δ × α) ⊕ (δ × β)) :=
by
  refine ⟨Distr α β δ, Distr_back, ?_, ?_⟩
  · funext x
    rw [comp_def, id_def]
    cases x with
    | inl da => rfl
    | inr db => rfl
  · funext ⟨d, x⟩
    rw [comp_def, id_def]
    cases x with
    | inl a => rfl
    | inr b => rfl

------------------------Sum-Ass------------------------

theorem iso_sum_ass {α β γ : Type}:
  ((α ⊕ β) ⊕ γ) ≅ (α ⊕ β ⊕ γ) :=
by
  refine ⟨Ass_sum_two, Ass_sum_one, ?_, ?_⟩
  · funext y
    rw [comp_def, id_def]
    cases y with
    | inl a => rfl
    | inr bc => cases bc with
                | inl b => rfl
                | inr c => rfl
  · funext x
    rw [comp_def, id_def]
    cases x with
    | inl ab => cases ab with
                | inl a => rfl
                | inr b => rfl
    | inr c => rfl

------------------------Sum-Com------------------------

theorem iso_sum_com {α β : Type}:
  (α ⊕ β) ≅ (β ⊕ α) :=
by
  refine ⟨Com_sum, Com_sum, ?_, ?_⟩
  · funext x
    rw [comp_def, id_def]
    cases x with
    | inr a => rfl
    | inl b => rfl
  · funext y
    rw [comp_def, id_def]
    cases y with
    | inr b => rfl
    | inl a => rfl

-------------------------Sum-Id-------------------------

theorem iso_sum_id {α : Type}:
  (α ⊕ 𝟘) ≅ α :=
by
  refine ⟨Id_sum, Sum_id, ?_, ?_⟩
  · funext a
    rw [comp_def, Sum_id, Id_sum, id_def]
  · funext x
    rw [comp_def, id_def]
    cases x with
    | inl a => rfl
    | inr e => contradiction

------------------------Prod-Ass------------------------

theorem iso_prod_ass {α β γ : Type}:
  ((α × β) × γ) ≅ (α × β × γ) :=
by
  refine ⟨Ass_prod_one, Ass_prod_two, ?_, ?_⟩
  · funext ⟨a, bc⟩
    rw [comp_def, Ass_prod_two, Ass_prod_one, id_def]
  · funext ⟨ab, c⟩
    rw [comp_def, Ass_prod_two, Ass_prod_one, id_def]

------------------------Prod-Com------------------------

theorem iso_prod_com {α β : Type}:
  (α × β) ≅ (β × α) :=
by
  refine ⟨Com_prod, Com_prod, ?_, ?_⟩
  · funext w
    rw [comp_def, Com_prod, Com_prod, id]
  · funext w'
    rw [comp_def, Com_prod, Com_prod, id]

------------------------Distr-R------------------------

theorem iso_distr_R {α β δ : Type}:
  ((α ⊕ β) × δ) ≅ ((α × δ) ⊕ (β × δ)) :=
by
  calc
    (α ⊕ β) × δ
    _ ≅ (δ × (α ⊕ β))       := iso_prod_com
    _ ≅ ((δ × α) ⊕ (δ × β)) := iso_distr_L
    _ ≅ ((α × δ) ⊕ (β × δ)) := iso_sum ⟨iso_prod_com, iso_prod_com⟩

-------------------------Prod-Id-------------------------

theorem iso_prod_id {α : Type}:
  (α × 𝟙) ≅ α :=
by
  refine ⟨Id_prod, prod_id, ?_, ?_⟩
  · funext a
    rw [comp_def, prod_id, Id_prod, id_def]
  · funext w
    rw [comp_def, Id_prod, prod_id, id_def]

------------------------Prod-Two-------------------------

theorem iso_prod_two {α : Type}:
  (𝟚 × α) ≅ (α ⊕ α) :=
by
  calc
    (𝟚 × α)
    _ ≅ ((𝟙 × α) ⊕ (𝟙 × α)) := iso_distr_R
    _ ≅ ((α × 𝟙) ⊕ (α × 𝟙)) := iso_sum ⟨iso_prod_com, iso_prod_com⟩
    _ ≅ (α ⊕ α)             := iso_sum ⟨iso_prod_id, iso_prod_id⟩

------------------------Prod-Anul------------------------

theorem iso_prod_anul {α : Type}:
  (α × 𝟘) ≅ 𝟘 :=
by
  refine ⟨prodToEmpty, toProdEmpty, ?_, ?_⟩
  · funext x
    nomatch x
  · funext x
    nomatch x.2

-----------------------Pow-Two-Sum-----------------------

theorem iso_pow_two_sum {α β : Type}:
  (𝟚 → α ⊕ β) ≅ ((𝟚 → α) ⊕ (𝟚 × α × β) ⊕ (𝟚 → β)) :=
by
  calc
    (𝟚 → α ⊕ β)
    _ ≅ ((α ⊕ β) × (α ⊕ β))                           := iso_pow_two
    _ ≅ ((α × (α ⊕ β)) ⊕ (β × (α ⊕ β)))              := iso_distr_R
    _ ≅ (((α × α) ⊕ (α × β)) ⊕ (β × α) ⊕ (β × β))    := iso_sum ⟨iso_distr_L, iso_distr_L⟩
    _ ≅ (((𝟚 → α) ⊕ (α × β)) ⊕ (α × β) ⊕ (𝟚 → β))    := iso_sum ⟨iso_sum ⟨iso_symm (𝟚 → α) (α × α) iso_pow_two, by apply iso_refl⟩, iso_sum ⟨iso_prod_com, iso_symm (𝟚 → β) (β × β) iso_pow_two⟩⟩
    _ ≅ ((𝟚 → α) ⊕ ((α × β) ⊕ (α × β) ⊕ (𝟚 → β)))    := iso_sum_ass
    _ ≅ ((𝟚 → α) ⊕ ((α × β) ⊕ (α × β)) ⊕ (𝟚 → β))    := iso_sum ⟨by apply iso_refl, iso_symm (((α × β) ⊕ (α × β)) ⊕ (𝟚 → β)) ((α × β) ⊕ (α × β) ⊕ (𝟚 → β)) iso_sum_ass⟩
    _ ≅ ((𝟚 → α) ⊕ (𝟚 × α × β) ⊕ (𝟚 → β))             := iso_sum ⟨by apply iso_refl, iso_sum ⟨iso_symm (𝟚 × α × β) ((α × β) ⊕ (α × β)) iso_prod_two, by apply iso_refl⟩⟩
