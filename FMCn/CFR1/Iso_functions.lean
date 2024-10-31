import FMCn.CFR1.Definitions
import FMCn.Intro_Lang_Proofs
import FMCn.CFR1.Useful

------------------------------------------------
--
------------------------------------------------

theorem iso_inj_sobr {α β : Type} {f : α → β} :
  iso_offun f → injetiva f ∧ sobrejetiva f :=
by
  intro h
  apply h.elim
  · intro f' h'
    refine ⟨?_, ?_⟩
    · intro a a' ha
      have h1 : (f' ∘ f) a = (f' ∘ f) a' :=
        by rw [Function.comp, Function.comp, univ f' ha]
      rw [h'.2, id, id] at h1
      exact h1
    · intro b
      exists (f' b)
      rw [← comp_def f' f, h'.1, id]

theorem inj_sobr_iso {α β : Type} {f : α → β} :
  injetiva f ∧ sobrejetiva f → iso_offun f :=
by
  apply impl_as_contrapositive_converse
  intro h h'
  sorry
