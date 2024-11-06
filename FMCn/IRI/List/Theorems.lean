import FMCn.IRI.List.Definitions
import FMCn.IRI.Nat.Theorems

namespace data

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
  | Nil => rw [concat, addNat, fmap, concat]
  | Cons k ks HI => rw [addNat] at HI
                    rw [concat, addNat, fmap,
                        HI, fmap, concat]

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

