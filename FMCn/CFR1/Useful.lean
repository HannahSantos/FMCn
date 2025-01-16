import FMCn.CFR1.Functions

namespace data
------------------------------------------------
-- Teoremas Auxiliares:
------------------------------------------------

theorem comp_def {α β γ: Type}:
  ∀ (f : α → β) (g : β → γ), ∀ (a : α), (g ⋄ f) a = g (f a) :=
by
  intro f g a
  rw [comp]

theorem id_def {α : Type} {x : α}:
  id x = x :=
by
  rw [id]

theorem id_comp {α β : Type}:
  ∀ (f : α → β), id ⋄ f = f ∧ f ⋄ id = f :=
by
  intro f
  apply And.intro
  · funext a
    rw [comp_def, id_def]
  · funext a'
    rw [comp_def, id_def]

theorem comp_assoc {α β γ δ : Type}:
  ∀ (f : α → β) (g : β → γ) (h : γ → δ), (h ⋄ g) ⋄ f= h ⋄ (g ⋄ f) :=
by
  intro f g h
  funext a
  rw [comp_def, comp_def,
      comp_def, comp_def]

theorem univ {α β : Type u} {a a' : α}:
  ∀ (f : α → β), a = a' → f a = f a' :=
by
  intro f h
  rw [h]

theorem univ_comp {f g : α → β} {h : β → γ} :
  f = g → h ⋄ f = h ⋄ g :=
by
  intro H
  rw [H]

theorem curry_fun {α β γ : Type} {f : α × β → γ} {a : α} {b : β} :
  curry f a b = f ⟨a, b⟩ :=
by
  rw [curry]

theorem uncurry_fun {α β γ : Type} {f : α → β → γ} {a : α} {b : β} :
  uncurry f ⟨a, b⟩ = f a b :=
by
  rw [uncurry]

theorem Fun_to_fun_def {α α' β β' : Type} {f : α' → α} {g : β → β'} {h : α → β}:
  Fun_to_fun f g h = g ⋄ h ⋄ f :=
by
  rw [Fun_to_fun]

theorem funext_hip {f g : α → β} {x : α} :
  f = g → f x = g x :=
by
  intro h
  rw [h]

theorem pairing_def {f : δ → α} {g : δ → β} {d : δ} :
  ⟪f, g⟫ d = ⟨f d, g d⟩ :=
by
  rw [pairing]

theorem prod_fun_def {f : α → γ} {g : β → δ} {a : α} {b : β} :
  (f × g) ⟨a, b⟩ = ⟨f a, g b⟩ :=
by
  rw [prod_fun]

theorem copairing_left {f : α → γ} {g : β → δ} {x : α}:
  (f ⊕ g) (.inl x) = .inl (f x) :=
by
  rw [copairing]

theorem copairing_right {f : α → γ} {g : β → δ} {x : β}:
  (f ⊕ g) (.inr x) = .inr (g x) :=
by
  rw [copairing]

theorem outl_def {a : α} {b : β} :
  outl ⟨a, b⟩ = a :=
by
  rw [outl]

theorem outr_def {a : α} {b : β} :
  outr ⟨a, b⟩ = b :=
by
  rw [outr]

theorem outl_pair {f : δ → α} {g : δ → β} :
  outl ⋄ ⟪f , g⟫ = f :=
by
  funext x
  rw [comp_def, pairing_def, outl_def]

theorem outr_pair {f : δ → α} {g : δ → β} :
  outr ⋄ ⟪f , g⟫ = g :=
by
  funext x
  rw [comp_def, pairing_def, outr_def]

theorem pairing_eq {f h : δ → α} {g k : δ → β} :
  ⟪f, g⟫ = ⟪h, k⟫ → f = h ∧ g = k :=
by
  intro H
  have HL : outl ⋄ ⟪f, g⟫ = outl ⋄ ⟪h, k⟫ := univ_comp H
  rw [outl_pair, outl_pair] at HL
  have HR : outr ⋄ ⟪f, g⟫ = outr ⋄ ⟪h, k⟫ := univ_comp H
  rw [outr_pair, outr_pair] at HR
  refine ⟨HL, HR⟩
