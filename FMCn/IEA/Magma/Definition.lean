class MagmaM (α : Type u) where
  opm : α × α → α
notation:75 a:75 " ⋆ " b:76 => MagmaM.opm ⟨a, b⟩

class MagmaA (α : Type u) where
  opa : α × α → α
notation:65 a:65 " ⊹ " b:66 => MagmaA.opa ⟨a, b⟩
