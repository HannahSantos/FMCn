def iso_offun {α β : Type} (f : α → β): Prop :=
  ∃ (g : β → α), f ∘ g = id ∧ g ∘ f = id

def injetiva {α β : Type} (f : α → β) : Prop :=
  ∀ (a a' : α), f a = f a' → a = a'

def sobrejetiva {α β : Type} (f : α → β) : Prop :=
  ∀ (b : β), ∃ (a : α), f a = b

def iso (α β : Type) : Prop :=
  ∃ (f : α → β) (g : β → α), f ∘ g = id ∧ g ∘ f = id
infix:50    " ≅ " => iso

variable {A : Type u}

def reflexive (R : A  → A → Prop) : Prop :=
∀ a, R a a

def symmetric (R : A → A → Prop) : Prop :=
∀ a b, R a b → R b a

def transitive (R : A → A → Prop) : Prop :=
∀ a b c, R a b → R b c → R a c

def equivalent_relation (R : A → A → Prop) : Prop :=
reflexive R ∧ symmetric R ∧ transitive R

def respects_empty : Prop :=
  Empty ≅ Empty

def respects_unit : Prop :=
  Unit ≅ Unit

def respects_sum : Prop :=
  ∀α α' β β', α ≅ α' ∧ β ≅ β' → (α ⊕ β) ≅ (α' ⊕ β')

def respects_prod : Prop :=
  ∀α α' β β', α ≅ α' ∧ β ≅ β' → (α × β) ≅ (α' × β')

def respects_fun : Prop :=
  ∀α α' β β', α ≅ α' ∧ β ≅ β' → (α → β) ≅ (α' → β')

def respects_algebric_structure : Prop :=
  respects_empty ∧ respects_unit ∧ respects_sum ∧ respects_prod ∧ respects_fun

def congruent : Prop :=
  equivalent_relation iso ∧ respects_algebric_structure
