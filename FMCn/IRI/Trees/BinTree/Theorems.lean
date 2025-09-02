import FMCn.IRI.Trees.BinTree.Definitions
import FMCn.IRI.Trees.BinTree.Useful
import FMCn.IRI.Nat.Theorems

namespace data
open BinTree

theorem BinTree.tips_Eq_succ_nodes (t : BinTree α) :
  .S (nodes t) = tips t :=
by
  induction t with
  | Leaf x => rw [nodes_leaf, tips_leaf]
  | Fork l r HL HR => rw [nodes_fork, tips_fork, ← HL,
                          ← HR, Nat.succ_add, Nat.add_succ]

theorem BinTree.depth_tips {t : BinTree α}:
  ((.S (.S .O)) ^ (depth t)) ≥ (tips t) :=
by
  induction t with
  | Leaf a => rw [tips_leaf, depth_leaf, Nat.pow_zero]
              apply Nat.geq_refl
  | Fork l r HL HR =>
    rw [depth_fork, tips_fork, Nat.pow_succ, Nat.mul_two]
    have h : Nat.max₂ (depth l) (depth r) = depth l ∨
             Nat.max₂ (depth l) (depth r) = depth r
      := Nat.max_opt (depth l) (depth r)
    apply h.elim
    · intro hl
      apply Nat.geq_simp hl HL HR
      · intro h'
        exact Nat.zero_ne_succ h'.symm
    · intro hr
      rw [Nat.max_com] at hr
      rw [Nat.max_com, Nat.add_com (tips l) (tips r)]
      apply Nat.geq_simp hr HR HL
      · intro h'
        exact Nat.zero_ne_succ h'.symm
