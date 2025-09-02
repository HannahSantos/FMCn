import FMCn.CFR1.Functions

namespace data

------------------------------------------------
-- Definições:
------------------------------------------------

def iso_offun {α β : Type} (f : α → β): Prop :=
  ∃ (g : β → α), (f ⋄ g) = id ∧ (g ⋄ f) = id

def injetiva {α β : Type} (f : α → β) : Prop :=
  ∀ (a a' : α), f a = f a' → a = a'

def sobrejetiva {α β : Type} (f : α → β) : Prop :=
  ∀ (b : β), ∃ (a : α), f a = b

def iso (α β : Type) : Prop :=
  ∃ (f : α → β) (g : β → α), f ⋄ g = id ∧ g ⋄ f = id
notation "(≅)" => iso
infix:40 " ≅ " => (≅)

variable {A : Type u}

def reflexive (R : A → A → Prop) : Prop :=
∀ a, R a a
notation R " is_refl" => reflexive R

def symmetric (R : A → A → Prop) : Prop :=
∀ a b, R a b → R b a
notation R " is_symm" => symmetric R

def transitive (R : A → A → Prop) : Prop :=
∀ a b c, R a b → R b c → R a c
notation R " is_trans" => transitive R

def antisymmetric (R : A → A → Prop) : Prop :=
∀ a b, R a b → R b a → a = b
notation R " is_antisymm" => antisymmetric R

def total (R : A → A → Prop) : Prop :=
∀ a b, R a b ∨ R b a
notation R " is_total" => total R

def equivalent_relation (R : A → A → Prop) : Prop :=
R is_refl ∧ R is_symm ∧ R is_trans
notation R " is_equivRel" => equivalent_relation R

def respects_empty : Prop :=
  𝟘 ≅ 𝟘
notation "(≅)-resp𝟘" => respects_empty

def respects_unit : Prop :=
  𝟙 ≅ 𝟙
notation "(≅)-resp𝟙" => respects_unit

def respects_sum : Prop :=
  ∀ {α α' β β' : Type}, α ≅ α' ∧ β ≅ β' → (α ⊕ β) ≅ (α' ⊕ β')
notation "(≅)-resp(⊕)" => respects_sum

def respects_prod : Prop :=
  ∀ {α α' β β' : Type}, α ≅ α' ∧ β ≅ β' → (α × β) ≅ (α' × β')
notation "(≅)-resp(×)" => respects_prod

def respects_fun : Prop :=
  ∀ {α α' β β' : Type}, α ≅ α' ∧ β ≅ β' → (α → β) ≅ (α' → β')
notation "(≅)-resp(→)" => respects_fun

def respects_algebric_structure : Prop :=
  (≅)-resp𝟘 ∧ (≅)-resp𝟙 ∧ (≅)-resp(⊕) ∧ (≅)-resp(×) ∧ (≅)-resp(→)
notation "(≅)-respAlgebStruct" => respects_algebric_structure

def congruent : Prop :=
  (≅) is_equivRel ∧ (≅)-respAlgebStruct
notation "(≅)-isCongr" => congruent
