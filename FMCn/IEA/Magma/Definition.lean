class Magma (α : Type u) where
  op : α × α → α
notation:65 a:65 " ⋆ " b:66 => Magma.op ⟨a, b⟩
