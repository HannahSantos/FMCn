import FMCn.IRI.Trees.BinTree.Definitions

namespace data
open Nat BinTree

----------------------------------------------------------
-- Nodes :
----------------------------------------------------------

theorem nodes_leaf :
  ∀ (x : α), nodes (Leaf x) = O :=
by
  intro _
  rw [nodes]

theorem nodes_fork :
  ∀ (l r : BinTree α), nodes (Fork l r) = S (nodes l + nodes r) :=
by
  intro l r
  rw [nodes]

----------------------------------------------------------
-- Tips :
----------------------------------------------------------

theorem tips_leaf :
  ∀ (x : α), tips (Leaf x) = S O :=
by
  intro _
  rw [tips]

theorem tips_fork :
  ∀ (l r : BinTree α), tips (Fork l r) = tips l + tips r :=
by
  intro l r
  rw [tips]

----------------------------------------------------------
-- Depth :
----------------------------------------------------------

theorem depth_leaf :
  ∀ (x : α), depth (Leaf x) = O :=
by
  intro _
  rw [depth]

theorem depth_fork :
  ∀ (l r : BinTree α), depth (Fork l r) = S (max₂ (depth l) (depth r)) :=
by
  intro l r
  rw [depth]
