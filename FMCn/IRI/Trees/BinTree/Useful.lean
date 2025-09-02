import FMCn.IRI.Trees.BinTree.Definitions

namespace data
open BinTree

----------------------------------------------------------
-- Nodes :
----------------------------------------------------------

theorem BinTree.nodes_leaf :
  ∀ (x : α), nodes (Leaf x) = .O :=
by
  intro _
  rw [nodes]

theorem BinTree.nodes_fork :
  ∀ (l r : BinTree α), nodes (Fork l r) = .S (nodes l + nodes r) :=
by
  intro l r
  rw [nodes]

----------------------------------------------------------
-- Tips :
----------------------------------------------------------

theorem BinTree.tips_leaf :
  ∀ (x : α), tips (Leaf x) = .S .O :=
by
  intro _
  rw [tips]

theorem BinTree.tips_fork :
  ∀ (l r : BinTree α), tips (Fork l r) = tips l + tips r :=
by
  intro l r
  rw [tips]

----------------------------------------------------------
-- Depth :
----------------------------------------------------------

theorem BinTree.depth_leaf :
  ∀ (x : α), depth (Leaf x) = .O :=
by
  intro _
  rw [depth]

theorem BinTree.depth_fork :
  ∀ (l r : BinTree α), depth (Fork l r) = .S (Nat.max₂ (depth l) (depth r)) :=
by
  intro l r
  rw [depth]
