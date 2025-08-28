import FMCn.IRI.List.Definitions
import FMCn.IRI.List.Useful
import FMCn.IRI.Nat.Theorems
import FMCn.IRI.FAM.Functor.Definitions
import FMCn.IRI.FAM.Applicative.Definitions
import FMCn.CFR1.Useful
import FMCn.IRI.Bool.Definitions
import FMCn.IRI.Bool.Theorems

namespace data.List

------------------------------------------------
-- List is a Functor
------------------------------------------------

theorem functor_list_id :
  ∀ (xs : ⟦α⟧), (Lmap id) xs = id xs:=
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
  | Cons k ks HI => rw [comp_def, Lmap, Lmap, Lmap, HI,
                        comp_def, comp_def]

instance : Functor List where
  fmap := Lmap
  Id_law := functor_list_id
  Comp_law := functor_list_comp

------------------------------------------------
-- Maybe Lists Theorems
------------------------------------------------

theorem just_eq {x y : ⟦α⟧} :
  Maybe.Just x = Maybe.Just y → x = y :=
by
  intro h
  have h' : stripMaybeL (Maybe.Just x) = stripMaybeL (Maybe.Just y)
    := univ stripMaybeL h
  rw [stripMaybeL] at h'
  exact h'

theorem safetail_cons {x : α} {xs : ⟦α⟧} :
  safetail (x∷xs) = .Just xs :=
by
  rw [safetail]

theorem cons_inj {x y : α} {xs ys : ⟦α⟧} :
  x∷xs = y∷ys → xs = ys :=
by
  intro h
  have h' : safetail (x∷xs) = safetail (y∷ys)
    := univ safetail h
  rw [safetail_cons, safetail_cons] at h'
  exact just_eq h'

------------------------------------------------
-- Append Theorems
------------------------------------------------

theorem append_eq_append_cat {n : α} {xs : ⟦α⟧} :
  append n xs = append_cat n xs :=
by
  induction xs with
  | Nil => rw [append_nil, append_cat_nil]
  | Cons k ks HI => rw [append_cons, HI, append_cat_def,
                        append_cat_cons]

theorem concat_append (x : α) (xs ys : ⟦α⟧) :
  ys ++ (append x xs) = append x (ys ++ xs) :=
by
  induction ys with
  | Nil => rw [concat, concat]
  | Cons k ks HI => rw [concat, HI, concat, append]

theorem reverse_append (x : α) (l : ⟦α⟧):
  reverse (append x l) = x∷reverse l :=
by
  induction l with
  | Nil => rw [append, reverse, reverse, reverse, append]
  | Cons k ks HI => rw [append, reverse, HI, append,
                        reverse]

theorem reverse_reverse (l : ⟦α⟧):
  reverse (reverse l) = l :=
by
  induction l with
  | Nil => rw [reverse_nil, reverse_nil]
  | Cons k ks HI => rw [reverse, reverse_append k
                        (reverse ks), HI]

theorem length_append (n : α) (l : ⟦α⟧):
  length (append n l) = .S (length l) :=
by
  induction l with
  | Nil => rw [append, length, length, length]
  | Cons k ks HI => rw [append, length, HI, length]

theorem length_reverse (l : ⟦α⟧):
  length (reverse l) = length l :=
by
  induction l with
  | Nil => rw [reverse]
  | Cons k ks HI => rw [reverse, length, length_append, HI]

------------------------------------------------
-- (++) Theorems
------------------------------------------------

theorem length_concat_distr (xs ys : ⟦α⟧) :
  length (xs ++ ys) = length xs + length ys :=
by
  induction xs with
  | Nil => rw [concat, length, Nat.zero_add]
  | Cons k ks HI => rw [concat, length, HI, length,
                        Nat.succ_add]

theorem reverse_concat (xs ys : ⟦α⟧) :
  reverse (xs ++ ys) = (reverse ys) ++ (reverse xs) :=
by
  induction xs with
  | Nil => rw [concat, reverse, concat_nil]
  | Cons k ks HI => rw [concat, reverse, HI,
                        reverse, concat_append]

theorem addNat_distr (n : Nat) (xs ys : ⟦Nat⟧) :
  addNat n (xs ++ ys) = (addNat n xs) ++ (addNat n ys) :=
by
  induction xs with
  | Nil => rw [nil_concat, addNat, Lmap, nil_concat]
  | Cons k ks HI => rw [addNat] at HI
                    rw [concat_cons, addNat, Lmap,
                        HI, Lmap, concat_cons]

theorem concat_assoc (xs ys zs : ⟦α⟧) :
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
by
  induction xs with
  | Nil => rw [concat, concat]
  | Cons k ks HI => rw [concat, concat, HI, concat]

------------------------------------------------
-- reverse, rev and revcat
------------------------------------------------

theorem rev_reverse :
  ∀ (xs : ⟦α⟧), reverse xs = rev xs :=
by
  intro xs
  induction xs with
  | Nil => rw [reverse, rev]
  | Cons k ks HI => rw [reverse, rev, HI, append_eq_append_cat,
                        append_cat_def]

theorem rev_to_revcat {xs : ⟦α⟧} :
  ∀ (l : ⟦α⟧), (rev xs) ++ l = revcat xs l :=
by
  induction xs with
  | Nil => intro ys
           rw [rev_nil, revcat_nil, nil_concat]
  | Cons k ks HI => intro ys
                    rw [rev_cons, concat_assoc, concat_cons,
                        nil_concat, HI (k∷ys), revcat_cons]

theorem rev_def {xs : ⟦α⟧} :
  rev xs = revcat xs (⟦⟧) :=
by
  rw [← rev_to_revcat, concat_nil]

------------------------------------------------
-- Sum/Product-Concat Theorems
------------------------------------------------

theorem sum_concat (xs ys : ⟦Nat⟧) :
  sum (xs ++ ys) = sum xs + sum ys :=
by
  induction xs with
  | Nil => rw [nil_concat, sum_nil, Nat.zero_add]
  | Cons k ks HI => rw [concat_cons, sum_cons, sum_cons,
                        HI, Nat.add_ass]

theorem product_concat (xs ys : ⟦Nat⟧) :
  product (xs ++ ys) = product xs * product ys :=
by
  induction xs with
  | Nil => rw [nil_concat, product_nil, Nat.one_mul]
  | Cons k ks HI => rw [concat_cons, product_cons, HI,
                        product_cons, Nat.mul_ass]

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

theorem zip_from_zipWith {ys : ⟦β⟧}:
  ∀ (xs : ⟦α⟧), zip xs ys = zipWith Prod.mk xs ys:=
by
  induction ys with
  | Nil => intro _
           rw [zip_nil, zipWith_nil]
  | Cons k ks HI =>
      intro xs
      cases xs with
      | Nil => rw [nil_zip, nil_zipWith]
      | Cons k' ks' => rw [zip, HI ks', zipWith]

theorem zipWith_from_zip {op : α → β → γ} {ys : ⟦β⟧}:
  ∀ (xs : ⟦α⟧), zipWith op xs ys = (Lmap (uncurry op) ⋄ zip xs) ys:=
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
