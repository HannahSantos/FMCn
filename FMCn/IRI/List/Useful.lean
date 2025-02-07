import FMCn.IRI.List.Definitions

namespace data

------------------------------------------------
-- Nil not Cons:
-----------------------------------------------

theorem nil_neq_cons {x : α} {xs : ‖α‖} :
  x∷xs ≠ ⟦⟧ :=
by
  intro h
  cases h

------------------------------------------------
-- (++) :
-----------------------------------------------

theorem nil_concat {l : ‖α‖} :
  (⟦⟧ : ‖α‖) ++ l = l :=
by
  rw [concat]

theorem concat_nil (l : ‖α‖) :
  l ++ (⟦⟧ : ‖α‖) = l :=
by
  induction l with
  | Nil => rw [concat]
  | Cons k ks HI => rw [concat, HI]

theorem Nil_concat_id (l : ‖α‖) :
  (⟦⟧ : ‖α‖) ++ l = l ∧ l ++ (⟦⟧ : ‖α‖) = l :=
by
  refine ⟨?_, ?_⟩
  rw [concat]
  rw [concat_nil]

theorem concat_cons {x : α} {xs ys : ‖α‖} :
  x∷xs ++ ys = x∷(xs ++ ys) :=
by
  rw [concat]

------------------------------------------------
-- Append :
-----------------------------------------------

theorem append_nil {n : α} :
  append n (⟦⟧ : ‖α‖) = ⟦n⟧ :=
by
  rw [append]

theorem append_cons {n x : α} {xs : ‖α‖} :
  append n (x∷xs) = x∷append n xs :=
by
  rw [append]

------------------------------------------------
-- Append_cat :
-----------------------------------------------

theorem append_cat_def {n : α} {xs : ‖α‖} :
  append_cat n xs = xs ++ ⟦n⟧ :=
by
  rw [append_cat]

theorem append_cat_nil {n : α} :
  append_cat n (⟦⟧) = ⟦n⟧ :=
by
  rw [append_cat_def, nil_concat]

theorem append_cat_cons {n x : α} {xs : ‖α‖} :
  append_cat n (x∷xs) = x∷(xs ++ ⟦n⟧) :=
by
  rw [append_cat_def, concat_cons]

------------------------------------------------
-- Reverse :
-----------------------------------------------

theorem reverse_nil :
  reverse (⟦⟧ : ‖α‖) = ⟦⟧ :=
by
  rw [reverse]

theorem reverse_cons {x : α} {xs : ‖α‖} :
  reverse (x∷xs) = append x (reverse xs):=
by
  rw [reverse]

------------------------------------------------
-- rev:
-----------------------------------------------

theorem rev_nil :
  rev (⟦⟧ : ‖α‖) = ⟦⟧ :=
by
  rw [rev]

theorem rev_cons {x : α} {xs : ‖α‖} :
  rev (x∷xs) = rev xs ++ ⟦x⟧ :=
by
  rw [rev]

------------------------------------------------
-- rev_cat:
-----------------------------------------------

theorem revcat_nil {ys : ‖α‖} :
  revcat (⟦⟧ : ‖α‖) ys = ys :=
by
  rw [revcat]

theorem revcat_cons {x : α} {xs ys : ‖α‖} :
  revcat (x∷xs) ys =  revcat xs (x∷ys) :=
by
  rw [revcat]

------------------------------------------------
-- sum :
-----------------------------------------------

theorem sum_nil :
  sum (⟦⟧ : ‖Nat‖) = .O :=
by
  rw [sum, FoldR]

theorem sum_cons (x : Nat) (xs : ‖Nat‖) :
  sum (x∷xs) = x + sum xs :=
by
  rw [sum, FoldR]

------------------------------------------------
-- product :
-----------------------------------------------

theorem product_nil :
  product (⟦⟧ : ‖Nat‖) = .S .O :=
by
  rw [product, FoldR]

theorem product_cons (x : Nat) (xs : ‖Nat‖) :
  product (x∷xs) = x * product xs :=
by
  rw [product, FoldR]

------------------------------------------------
-- zip :
-----------------------------------------------

theorem zip_nil {xs : ‖α‖} :
  zip xs (⟦⟧ : ‖β‖) = ⟦⟧ :=
by
  rw [zip]
  intro _ _ _ _ _ h
  exact (nil_neq_cons h.symm)

theorem nil_zip {ys : ‖β‖} :
  zip (⟦⟧ : ‖α‖) ys = ⟦⟧ :=
by
  rw [zip]
  intro _ _ _ _ h _
  exact (nil_neq_cons h.symm)

------------------------------------------------
-- zipWith :
-----------------------------------------------

theorem zipWith_nil {op : α → β → γ} {xs : ‖α‖} :
  zipWith op xs (⟦⟧) = ⟦⟧ :=
by
  rw [zipWith]
  intro _ _ _ _ _ h
  exact (nil_neq_cons h.symm)

theorem nil_zipWith {op : α → β → γ} {ys : ‖β‖} :
  zipWith op (⟦⟧) ys = ⟦⟧ :=
by
  rw [zipWith]
  intro _ _ _ _ h _
  exact (nil_neq_cons h.symm)
