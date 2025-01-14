import FMCn.IRI.Trees.BinTree.Definitions
import FMCn.IRI.Nat.Theorems

namespace data
open BinTree

theorem tips_Eq_succ_nodes (t : BinTree α) :
  .S (nodes t) = tips t :=
by
  induction t with
  | Leaf x => rw [nodes, tips]
  | Fork l r HL HR => rw [nodes, tips, ← HL, ← HR, Add_succ_L, add]
