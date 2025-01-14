import FMCn.IRI.List.Definitions
import FMCn.IRI.Nat.Theorems
import FMCn.IRI.FAM.Functor.Definitions
import FMCn.IRI.FAM.Applicative.Definitions
import FMCn.CFR1.Useful
import FMCn.IRI.Bool.Definitions
import FMCn.IRI.Bool.Theorems

namespace data

------------------------------------------------
-- List is a Functor
------------------------------------------------

theorem functor_list_id :
  ∀ (xs : ‖α‖), (Lmap id) xs = id xs:=
by
  intro xs
  induction xs with
  | Nil => rw [id_def, Lmap]
  | Cons k ks HI => rw [id_def, Lmap, id_def, HI, id_def]

theorem functor_list_comp {f : β → γ} {g : α → β}:
  Lmap (f ⋄ g) = Lmap f ⋄ Lmap g :=
by
  funext xs
  induction xs with
  | Nil => rw [Lmap, comp_def, Lmap, Lmap]
  | Cons k ks HI => rw [comp_def, Lmap, Lmap, Lmap, HI, comp_def, comp_def]

instance : Functor List where
  fmap := Lmap
  Id_law := functor_list_id
  Comp_law := functor_list_comp

------------------------------------------------
-- Fun Theorems
------------------------------------------------

theorem reverse_nil :
  reverse (⟦⟧ : ‖α‖) = ⟦⟧ :=
by
  rw [reverse]

theorem concat_nil (l : ‖α‖) :
  l ++ (⟦⟧ : ‖α‖) = l :=
by
  induction l with
  | Nil => rw [concat]
  | Cons k ks HI => rw [concat, HI]

theorem sum_nil :
  sum (⟦⟧ : ‖Nat‖) = .O :=
by
  rw [sum, FoldR]

theorem sum_cons (x : Nat) (xs : ‖Nat‖) :
  sum (x∷xs) = x + sum xs :=
by
  rw [sum, FoldR]

theorem product_nil :
  product (⟦⟧ : ‖Nat‖) = .S .O :=
by
  rw [product, FoldR]

theorem product_cons (x : Nat) (xs : ‖Nat‖) :
  product (x∷xs) = x * product xs :=
by
  rw [product, FoldR]

theorem concat_append (x : α) (xs ys : ‖α‖) :
  ys ++ (append x xs) = append x (ys ++ xs) :=
by
  induction ys with
  | Nil => rw [concat, concat]
  | Cons k ks HI => rw [concat, HI, concat, append]

theorem reverse_append (x : α) (l : ‖α‖):
  reverse (append x l) = x∷reverse l :=
by
  induction l with
  | Nil => rw [append, reverse, reverse, reverse, append]
  | Cons k ks HI => rw [append, reverse, HI, append, reverse]

theorem reverse_reverse (l : ‖α‖):
  reverse (reverse l) = l :=
by
  induction l with
  | Nil => rw [reverse_nil, reverse_nil]
  | Cons k ks HI => rw [reverse, reverse_append k (reverse ks), HI]

theorem length_append (n : α) (l : ‖α‖):
  length (append n l) = .S (length l) :=
by
  induction l with
  | Nil => rw [append, length, length, length]
  | Cons k ks HI => rw [append, length, HI, length]

theorem length_reverse (l : ‖α‖):
  length (reverse l) = length l :=
by
  induction l with
  | Nil => rw [reverse]
  | Cons k ks HI => rw [reverse, length, length_append, HI]

theorem length_concat_distr (xs ys : ‖α‖) :
  length (xs ++ ys) = length xs + length ys :=
by
  induction xs with
  | Nil => rw [concat, length, Add_zero_L]
  | Cons k ks HI => rw [concat, length, HI, length, Add_succ_L]

theorem reverse_concat_concat_reverse (xs ys : ‖α‖) :
  reverse (xs ++ ys) = (reverse ys) ++ (reverse xs) :=
by
  induction xs with
  | Nil => rw [concat, reverse, concat_nil]
  | Cons k ks HI => rw [concat, reverse, HI, reverse, concat_append]

theorem addNat_distr (n : Nat) (xs ys : ‖Nat‖) :
  addNat n (concat xs ys) = (addNat n xs) ++ (addNat n ys) :=
by
  induction xs with
  | Nil => rw [concat, addNat, Lmap, concat]
  | Cons k ks HI => rw [addNat] at HI
                    rw [concat, addNat, Lmap,
                        HI, Lmap, concat]

theorem concat_assoc (xs ys zs : ‖α‖) :
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
by
  induction xs with
  | Nil => rw [concat, concat]
  | Cons k ks HI => rw [concat, concat, HI, concat]

theorem Nil_concat_id (l : ‖α‖) :
  (⟦⟧ : ‖α‖) ++ l = l ∧ l ++ (⟦⟧ : ‖α‖) = l :=
by
  refine ⟨?_, ?_⟩
  rw [concat]
  rw [concat_nil]

theorem rev_to_revcat (xs : ‖α‖):
  ∀ (l : ‖α‖), (rev xs) ++ l = revcat xs l :=
by
  induction xs with
  | Nil => intro ys
           rw [rev, revcat, concat]
  | Cons k ks HI => intro ys
                    rw [rev, concat_assoc, concat,
                        concat, HI (k∷ys), revcat]


------------------------------------------------
-- More Theorems
------------------------------------------------

theorem sum_concat (xs ys : ‖Nat‖) :
  sum (xs ++ ys) = sum xs + sum ys :=
by
  induction xs with
  | Nil => rw [concat, sum_nil, Add_zero_L]
  | Cons k ks HI => rw [concat, sum_cons, sum_cons, HI, Add_Ass]

theorem product_concat (xs ys : ‖Nat‖) :
  product (xs ++ ys) = product xs * product ys :=
by
  induction xs with
  | Nil => rw [concat, product_nil, Mul_Id_L]
  | Cons k ks HI => rw [concat, product_cons, HI, product_cons, Mul_Ass]

------------------------------------------------
-- Foldable Functions
------------------------------------------------

theorem Any_to_FoldR (p : α → Bool) :
  Any p = FoldR (bor ⋄ p) .false :=
by
  funext xs
  induction xs with
  | Nil => rw [Any, FoldR]
  | Cons k ks HI => rw [Any, HI, FoldR, comp_def]

theorem All_to_FoldR (p : α → Bool) :
  All p = FoldR (band ⋄ p) .true :=
by
  funext xs
  induction xs with
  | Nil => rw [All, FoldR]
  | Cons k ks HI => rw [All, HI, FoldR, comp_def]

theorem Lmap_to_FoldR (f : α → β) :
  Lmap f = FoldR (.Cons ⋄ f) (⟦⟧) :=
by
  funext xs
  induction xs with
  | Nil => rw [Lmap, FoldR]
  |Cons k ks HI => rw [Lmap, HI, FoldR, comp_def]

------------------------------------------------
-- zip and zipWith
------------------------------------------------

theorem nil_neq_cons {x : α} {xs : ‖α‖} :
  x∷xs ≠ ⟦⟧ :=
by
  intro h
  cases h

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

theorem zip_from_zipWith {ys : ‖β‖}:
  ∀ (xs : ‖α‖), zip xs ys = zipWith Prod.mk xs ys:=
by
  induction ys with
  | Nil => intro _
           rw [zip_nil, zipWith_nil]
  | Cons k ks HI =>
      intro xs
      cases xs with
      | Nil => rw [nil_zip, nil_zipWith]
      | Cons k' ks' => rw [zip, HI ks', zipWith]

theorem zipWith_from_zip {op : α → β → γ} {ys : ‖β‖}:
  ∀ (xs : ‖α‖), zipWith op xs ys = (Lmap (uncurry op) ⋄ zip xs) ys:=
by
  induction ys with
  | Nil => intro _
           rw [comp_def, zip_nil, zipWith_nil, Lmap]
  | Cons k ks HI =>
      intro xs
      cases xs with
      | Nil => rw [comp_def, nil_zipWith, nil_zip, Lmap]
      | Cons k' ks' => rw [comp_def, zipWith, zip, Lmap,
                           uncurry_fun, HI ks', comp_def]
