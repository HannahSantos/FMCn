import FMCn.IRI.Trees.LBTree.Definitions
import FMCn.IRI.List.Definitions
import FMCn.IRI.List.Theorems
import FMCn.IRI.Trees.LBTree.Useful

namespace data

open LBTree

-----------------------------------------------------------
-- Flatten and Flatten' :
-----------------------------------------------------------

theorem flatten'_flat {t : LBTree α β} :
  ∀ (xs : ‖α ⊕ β‖), flatten t ++ xs = flatten' t xs :=
by
  induction t with
  | Tip a => intro xs
             rw [flatten_tip, concat,
                 concat, flatten'_tip]
  | Fork b l r HL HR =>
    intro xs
    rw [flatten_fork, flatten'_fork, concat_assoc,
        concat, HR xs, HL (Sum.inr b∷flatten' r xs)]

theorem flatten_def {t : LBTree α β} :
  flatten t = flatten' t (⟦⟧) :=
by
  rw [← concat_nil (flatten t), flatten'_flat]

-----------------------------------------------------------
-- Fun:
-----------------------------------------------------------

theorem rev_mirror {t : LBTree α β}:
  (flatten ⋄ mirror) t = (rev ⋄ flatten) t :=
by
  rw [comp_def, comp_def]
  induction t with
  | Tip a => rw [mirror_tip, flatten_tip, rev_def,
                 revcat_cons, revcat_nil]
  | Fork b l r HL HR =>
    rw [mirror_fork, flatten_fork, HL, HR, flatten_fork,
        ← rev_reverse (flatten l ++ Sum.inr b∷flatten r),
        reverse_concat, rev_reverse, rev_reverse, rev_cons,
        concat_assoc, concat_cons, nil_concat]
