import FMCn.IRI.Trees.BinTree.Definitions
import FMCn.IRI.Trees.BinTree.Useful
import FMCn.IRI.Nat.Theorems

namespace data
open BinTree Nat

theorem tips_Eq_succ_nodes (t : BinTree α) :
  S (nodes t) = tips t :=
by
  induction t with
  | Leaf x => rw [nodes_leaf, tips_leaf]
  | Fork l r HL HR => rw [nodes_fork, tips_fork, ← HL,
                          ← HR, succ_add, add_succ]

theorem depth_tips {t : BinTree α}:
  ((S (S O)) ^ (depth t)) ≥ (tips t) :=
by
  induction t with
  | Leaf a => rw [tips_leaf, depth_leaf, pow_zero]
              apply geq_refl
  | Fork l r HL HR =>
    rw [depth_fork, tips_fork, pow_succ, mul_two]
    have h : max₂ (depth l) (depth r) = depth l ∨
             max₂ (depth l) (depth r) = depth r
      := max_opt (depth l) (depth r)
    apply h.elim
    · intro hl
      apply geq_simp hl HL HR
      · intro h'
        exact zero_ne_succ h'.symm
    · intro hr
      rw [max_com] at hr
      rw [max_com, add_com (tips l) (tips r)]
      apply geq_simp hr HR HL
      · intro h'
        exact zero_ne_succ h'.symm
