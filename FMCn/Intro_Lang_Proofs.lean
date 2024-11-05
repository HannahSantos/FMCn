section propositional

variable (P Q R : Prop)

----------------------------------------------------------
-- Reflexividade da →:
----------------------------------------------------------

theorem impl_refl :
  P → P  :=
by
  intro p
  exact p

----------------------------------------------------------
-- Weakening and contraction:
----------------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
by
  intro p
  apply Or.inl p

theorem weaken_disj_left :
  Q → (P∨Q)  :=
by
  intro q
  apply Or.inr q

theorem weaken_conj_right :
  (P∧Q) → P  :=
by
  intro hpaq
  exact hpaq.1

theorem weaken_conj_left :
  (P∧Q) → Q  :=
by
  intro hpaq
  exact hpaq.2

theorem conj_idempot :
  (P∧P) ↔ P :=
by
  apply Iff.intro
  · exact weaken_conj_left P P
  · intro p
    apply And.intro p p

theorem disj_idempot :
  (P∨P) ↔ P  :=
by
  apply Iff.intro
  · intro hpop
    apply hpop.elim
    · exact impl_refl P
    · exact impl_refl P
  · exact weaken_disj_left P P

----------------------------------------------------------
-- Proposições de dupla negaço:
----------------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
by
  intro p np
  exact np p

theorem doubleneg_elim :
  ¬¬P → P  :=
by
  intro nnp
  by_cases p : P
  · exact p
  · exact False.elim (nnp p)

theorem doubleneg_law :
  ¬¬P ↔ P  :=
by
  refine ⟨doubleneg_elim P, doubleneg_intro P⟩

----------------------------------------------------------
-- Comutatividade dos ∨,∧:
----------------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
by
  intro hpoq
  apply hpoq.elim
  · intro p
    apply Or.inr p
  · intro q
    apply Or.inl q

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
by
  intro hpaq
  exact ⟨hpaq.2, hpaq.1⟩

----------------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
----------------------------------------------------------

theorem impl_as_disj :
  (P → Q) → (¬P ∨ Q) :=
by
  intro hpq
  by_cases p : P
  · apply Or.inr (hpq p)
  · apply Or.inl p

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
by
  intro hnpoq p
  apply hnpoq.elim
  · intro np
    exact False.elim (np p)
  · exact impl_refl Q

theorem neg_impl_as_neg_disj :
  ¬(P → Q) → ¬(¬P ∨ Q) :=
by
  intro nhpq hnpoq
  exact nhpq (impl_as_disj_converse P Q hnpoq)

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
by
  intro hpoq np
  apply hpoq.elim
  · intro p
    exact False.elim (np p)
  · exact impl_refl Q

----------------------------------------------------------
-- Proposições de contraposição:
----------------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
by
  intro hpiq nq p
  exact nq (hpiq p)

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
by
  intro hnqinp p
  by_cases q : Q
  · exact q
  · exact False.elim ((hnqinp q) p)

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
by
  refine ⟨impl_as_contrapositive P Q, impl_as_contrapositive_converse P Q⟩

----------------------------------------------------------
-- TO_DO: Nome
----------------------------------------------------------

theorem russel_problem :
  ¬(P ↔ ¬P)  :=
by
  intro hpbnp
  suffices np : ¬ P from np (hpbnp.2 np)
  · intro p
    exact (hpbnp.1 p) p

----------------------------------------------------------
-- A irrefutabilidade do LEM:
----------------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P ∨ ¬P)  :=
by
  intro nhponp
  suffices hponp : P ∨ ¬P from nhponp hponp
  · apply Or.inr
    intro p
    have hponp' : P ∨ ¬P := by
      exact weaken_disj_right P (¬ P) p
    exact nhponp hponp'

----------------------------------------------------------
-- A lei de Peirce
----------------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
by
  intro h_piq_ip np
  suffices hpiq : P → Q from np (h_piq_ip hpiq)
  · intro p
    exact False.elim (np p)

theorem peirce_law :
  ((P → Q) → P) → P  :=
by
  intro h_piq_ip
  exact doubleneg_elim P (peirce_law_weak P Q h_piq_ip)

----------------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
----------------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
by
  intro hpoq hnpanq
  apply hpoq.elim
  · intro p
    exact hnpanq.1 p
  · intro q
    exact hnpanq.2 q

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
by
  intro hpaq hnponq
  apply hnponq.elim
  · intro np
    exact np hpaq.1
  · intro nq
    exact nq hpaq.2

----------------------------------------------------------
-- As leis de De Morgan para ∨,∧:
----------------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
by
  intro nhpoq
  apply And.intro
  · intro p
    suffices hpoq : P ∨ Q from nhpoq hpoq
    · exact weaken_disj_right P Q p
  · intro q
    suffices hpoq : P ∨ Q from nhpoq hpoq
    · exact weaken_disj_left P Q q

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
by
  intro hnpanq hpoq
  apply hpoq.elim
  · intro p
    exact hnpanq.1 p
  · intro q
    exact hnpanq.2 q

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
by
  intro nhpaq
  by_cases p : P
  · apply Or.inl
    intro q
    exact False.elim (nhpaq ⟨p, q⟩)
  · apply Or.inr
    exact p

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
by
  intro hnqonp hpaq
  apply hnqonp.elim
  · intro nq
    exact nq hpaq.2
  · intro np
    exact np hpaq.1

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
by
  refine ⟨demorgan_conj P Q, demorgan_conj_converse P Q⟩

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
by
  refine ⟨demorgan_disj P Q, demorgan_disj_converse P Q⟩

----------------------------------------------------------
-- LEA:
----------------------------------------------------------

theorem lea :
  (P → Q) ∨ (Q → P) :=
by
  by_cases h : P → Q
  · apply Or.inl h
  · apply Or.inr
    intro q
    suffices h' : (P → Q) from False.elim (h h')
    · intro
      exact q

theorem total_arrow :
  (P → Q) ∨ (Q → P) :=
by
  by_cases p : P
  · apply Or.inr
    intro
    exact p
  · apply Or.inl
    intro p'
    exact False.elim (p p')

theorem iff_negtodisj_conj_neg :
  (¬P ↔ P ∨ Q) → ¬P ∧ Q :=
by
  intro h
  refine ⟨?_, ?_⟩
  · intro p
    suffices hpoq : P ∨ Q from (h.2 hpoq) p
    · apply Or.inl p
  · by_cases p : P
    · suffices hpoq : P ∨ Q from False.elim ((h.2 hpoq) p)
      · apply Or.inl p
    · have hpoq : P ∨ Q := h.1 p
      apply hpoq.elim
      · intro p'
        exact False.elim (p p')
      · exact impl_refl Q

----------------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
----------------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
by
  intro hpa_qor
  apply hpa_qor.2.elim
  · intro q
    apply Or.inl ⟨hpa_qor.1, q⟩
  · intro r
    apply Or.inr ⟨hpa_qor.1, r⟩

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
by
  intro hpaqopar
  apply hpaqopar.elim
  · intro hpaq
    refine ⟨hpaq.1, Or.inl hpaq.2⟩
  · intro hpar
    refine ⟨hpar.1, Or.inr hpar.2⟩

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
by
  intro hpo_qar
  apply hpo_qar.elim
  · intro p
    refine ⟨Or.inl p, Or.inl p⟩
  · intro hqar
    refine ⟨Or.inr hqar.1, Or.inr hqar.2⟩

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
by
  intro hpoq_a_por
  apply hpoq_a_por.1.elim
  · intro p
    apply Or.inl p
  · intro q
    apply hpoq_a_por.2.elim
    · intro p
      apply Or.inl p
    · intro r
      apply Or.inr ⟨q, r⟩

----------------------------------------------------------
-- Currificação
----------------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
by
  intro hpaqir p q
  exact hpaqir ⟨p, q⟩

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
by
  intro hpiqir hpaq
  exact hpiqir hpaq.1 hpaq.2

----------------------------------------------------------
-- Extras
----------------------------------------------------------

theorem impl_conj_impl_iff :
  (P∧Q → Q∧R) ↔ (P∧Q → R) :=
by
  refine ⟨?_, ?_⟩
  · intro hpaqiqar hpaq
    exact (hpaqiqar hpaq).2
  · intro hpaqir hpaq
    exact ⟨hpaq.2, hpaqir hpaq⟩

end propositional


------------------------------------------------------------------


section predicate

variable (α : Type)
variable (P : Prop)
variable (φ ψ : α -> Prop)


----------------------------------------------------------
-- As leis de De Morgan para ∃,∀:
----------------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, φ x) → (∀x, ¬φ x)  :=
by
  intro nhe a pa
  suffices he : ∃x, φ x from nhe he
  · exact ⟨a, pa⟩

theorem demorgan_exists_converse :
  (∀x, ¬φ x) → ¬(∃x, φ x)  :=
by
  intro hfn he
  apply he.elim
  intro a pa
  suffices npa : ¬φ a from npa pa
  · apply hfn a

theorem demorgan_forall :
  ¬(∀x, φ x) → (∃x, ¬φ x)  :=
by
  intro nha
  apply Classical.byContradiction
  · intro nhen
    suffices ha : ∀x, φ x from nha ha
    · intro a
      by_cases pa : φ a
      · exact pa
      · suffices hen : ∃x, ¬φ x from False.elim (nhen hen)
        · exact ⟨a, pa⟩

theorem demorgan_forall_converse :
  (∃x, ¬φ x) → ¬(∀x, φ x)  :=
by
  intro hen ha
  apply hen.elim
  intro a npa
  exact npa (ha a)

theorem demorgan_forall_law :
  ¬(∀x, φ x) ↔ (∃x, ¬φ x)  :=
by
  refine ⟨demorgan_forall α φ, demorgan_forall_converse α φ⟩

theorem demorgan_exists_law :
  ¬(∃x, φ x) ↔ (∀x, ¬φ x)  :=
by
  refine ⟨demorgan_exists α φ, demorgan_exists_converse α φ⟩

----------------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
----------------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, φ x) → ¬(∀x, ¬φ x)  :=
by
  intro he han
  apply he.elim
  intro a pa
  exact (han a) pa

theorem forall_as_neg_exists :
  (∀x, φ x) → ¬(∃x, ¬φ x)  :=
by
  intro ha hen
  apply hen.elim
  intro a npa
  exact npa (ha a)

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬φ x) → (∀x, φ x)  :=
by
  intro nhen a
  by_cases pa : φ a
  · exact pa
  · suffices hen : ∃x, ¬φ x from False.elim (nhen hen)
    · exact ⟨a, pa⟩

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬φ x) → (∃x, φ x)  :=
by
  intro nhan
  apply Classical.byContradiction
  · intro nhe
    suffices han : ∀x, ¬φ x from nhan han
    · intro a pa
      suffices he : ∃x, φ x from nhe he
      · exact ⟨a, pa⟩

theorem forall_as_neg_exists_law :
  (∀x, φ x) ↔ ¬(∃x, ¬φ x)  :=
by
  refine ⟨forall_as_neg_exists α φ, forall_as_neg_exists_converse α φ⟩

theorem exists_as_neg_forall_law :
  (∃x, φ x) ↔ ¬(∀x, ¬φ x)  :=
by
  refine ⟨exists_as_neg_forall α φ, exists_as_neg_forall_converse α φ⟩

----------------------------------------------------------
--  Proposições de distributividade de quantificadores:
----------------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, φ x ∧ ψ x) → (∃x, φ x) ∧ (∃x, ψ x)  :=
by
  intro hepas
  apply hepas.elim
  intro a hps
  refine ⟨⟨a, hps.1⟩,⟨a, hps.2⟩⟩

theorem exists_disj_as_disj_exists :
  (∃x, φ x ∨ ψ x) → (∃x, φ x) ∨ (∃x, ψ x)  :=
by
  intro hepos
  apply hepos.elim
  intro a hpos
  apply hpos.elim
  · intro pa
    apply Or.inl ⟨a, pa⟩
  · intro sa
    apply Or.inr ⟨a, sa⟩

theorem exists_disj_as_disj_exists_converse :
  (∃x, φ x) ∨ (∃x, ψ x) → (∃x, φ x ∨ ψ x)  :=
by
  intro hepohes
  apply hepohes.elim
  · intro hep
    apply hep.elim
    intro a pa
    refine ⟨a, Or.inl pa⟩
  · intro hes
    apply hes.elim
    intro a sa
    refine ⟨a, Or.inr sa⟩

theorem forall_conj_as_conj_forall :
  (∀x, φ x ∧ ψ x) → (∀x, φ x) ∧ (∀x, ψ x)  :=
by
  intro hapas
  refine ⟨?_, ?_⟩
  · intro a
    exact (hapas a).1
  · intro a
    exact (hapas a).2

theorem forall_conj_as_conj_forall_converse :
  (∀x, φ x) ∧ (∀x, ψ x) → (∀x, φ x ∧ ψ x)  :=
by
  intro hapahas a
  refine ⟨hapahas.1 a, hapahas.2 a⟩

theorem forall_disj_as_disj_forall_converse :
  (∀x, φ x) ∨ (∀x, ψ x) → (∀x, φ x ∨ ψ x)  :=
by
  intro hapohas a
  apply hapohas.elim
  · intro hap
    apply Or.inl (hap a)
  · intro has
    apply Or.inr (has a)

------------------------------------------------
-- Extras:
------------------------------------------------

theorem forall_placement_iff :
  P → (∀x, ψ x) ↔ (∀x, P → ψ x) :=
by
  refine ⟨?_, ?_⟩
  · intro hpas a p
    exact hpas p a
  · intro haps p a
    exact haps a p

/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=

---------------------------------------------- -/

end predicate
