import FMCn.IRI.List.Definitions
import FMCn.IRI.Trees.LBTree.Definitions

namespace data

open LBTree

-----------------------------------------------------------
-- Flatten :
-----------------------------------------------------------

theorem flatten_tip {a : α}:
  flatten (Tip a : LBTree α β) = ⟦.inl a⟧ :=
by
  rw [flatten]

theorem flatten_fork {b : β} {l r : LBTree α β} :
  flatten (Fork b l r) = flatten l ++ .inr b∷flatten r :=
by
  rw [flatten]

-----------------------------------------------------------
-- Flatten' :
-----------------------------------------------------------

theorem flatten'_tip {a : α} {xs : ⟦α ⊕ β⟧} :
  flatten' (Tip a : LBTree α β) xs = .inl a∷xs :=
by
  rw [flatten']

theorem flatten'_fork {b : β} {l r : LBTree α β} {xs : ⟦α ⊕ β⟧} :
  flatten' (Fork b l r) xs = flatten' l (.inr b∷flatten' r xs) :=
by
  rw [flatten']

-----------------------------------------------------------
-- Mirror :
-----------------------------------------------------------

theorem mirror_tip {a : α} :
  mirror (Tip a : LBTree α β) = Tip a :=
by
  rw [mirror]

theorem mirror_fork {b : β} {l r : LBTree α β} :
  mirror (Fork b l r) = Fork b (mirror r) (mirror l) :=
by
  rw [mirror]
