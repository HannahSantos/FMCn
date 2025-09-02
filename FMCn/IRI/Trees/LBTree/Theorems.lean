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
  ∀ (xs : ⟦α ⊕ β⟧), flatten t ++ xs = flatten' t xs :=
by
  induction t with
  | Tip a => intro xs
             rw [flatten_tip, List.concat_cons,
                 List.nil_concat, flatten'_tip]
  | Fork b l r HL HR =>
    intro xs
    rw [flatten_fork, flatten'_fork, List.concat_assoc,
        List.concat_cons, HR xs, HL (Sum.inr b∷flatten' r xs)]

theorem flatten_def {t : LBTree α β} :
  flatten t = flatten' t (⟦⟧) :=
by
  rw [← List.concat_nil (flatten t), flatten'_flat]

-----------------------------------------------------------
-- Fun:
-----------------------------------------------------------

theorem rev_mirror {t : LBTree α β}:
  (flatten ⋄ mirror) t = (List.rev ⋄ flatten) t :=
by
  rw [comp_def, comp_def]
  induction t with
  | Tip a => rw [mirror_tip, flatten_tip, List.rev_def,
                 List.revcat_cons, List.revcat_nil]
  | Fork b l r HL HR =>
    rw [mirror_fork, flatten_fork, HL, HR, flatten_fork,
        ← List.rev_reverse (flatten l ++ Sum.inr b∷flatten r),
        List.reverse_concat, List.rev_reverse, List.rev_reverse,
        List.rev_cons, List.concat_assoc, List.concat_cons, List.nil_concat]
