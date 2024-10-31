------------------------------------------------
-- Teoremas Auxiliares:
------------------------------------------------

theorem comp_def {α β γ: Type}:
  ∀ (f : α → β) (g : β → γ), ∀ (a : α), (g ∘ f) a = g (f a) :=
by
  intro f g a
  rw [Function.comp]

theorem id_comp {α β : Type}:
  ∀ (f : α → β), id ∘ f = f ∧ f ∘ id = f :=
by
  intro f
  apply And.intro
  · funext a
    rw [Function.comp, id]
  · funext a'
    rw [Function.comp, id]

theorem comp_assoc {α β γ δ : Type}:
  ∀ (f : α → β) (g : β → γ) (h : γ → δ), (h ∘ g) ∘ f= h ∘ (g ∘ f) :=
by
  intro f g h
  funext a
  rw [Function.comp, Function.comp,
      Function.comp, Function.comp]

theorem univ {α β : Type} {a a' : α}:
  ∀ (f : α → β), a = a' → f a = f a' :=
by
  intro f h
  rw [h]
