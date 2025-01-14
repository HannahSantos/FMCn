import FMCn.CFR1.Definitions
import FMCn.Intro_Lang_Proofs
import FMCn.CFR1.Useful

namespace data

------------------------------------------------
--
------------------------------------------------
theorem iso_L_cancel {α β : Type} {f : α → β} :
  iso_offun f → ∃ (g : β → α), (g ⋄ f) = id :=
by
  intro h
  apply h.elim
  · intro f' h'
    refine ⟨f', h'.2⟩

theorem iso_R_cancel {α β : Type} {f : α → β} :
  iso_offun f → ∃ (g : β → α), (f ⋄ g) = id :=
by
  intro h
  apply h.elim
  · intro f' h'
    refine ⟨f', h'.1⟩

theorem iso_inj_sobr {α β : Type} {f : α → β} :
  iso_offun f → injetiva f ∧ sobrejetiva f :=
by
  intro h
  apply h.elim
  · intro f' h'
    refine ⟨?_, ?_⟩
    · intro a a' ha
      have h1 : (f' ⋄ f) a = (f' ⋄ f) a' :=
        by rw [comp_def, comp_def, univ f' ha]
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
