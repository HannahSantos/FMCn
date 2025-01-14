import FMCn.IEA.Monoid.Definitions

class has_Inv (α : Type u) where inv : α → α
postfix:max "⁻¹"  => has_Inv.inv
open has_Inv

class Group (α : Type u) extends Monoid α, has_Inv α where
  Op_Inv_L : ∀ (a : α), a⁻¹ ⋆ a = e
  Op_Inv_R : ∀ (a : α), a ⋆ a⁻¹ = e
open Monoid Group

def invG [Group G] (x a : G): Prop :=
  x ⋆ a = e ∧ a ⋆ x = e
notation:65 a:65 " é o inverso de " b:66 => invG a b

------------------------------------------------
-- Group-Homomorphisms :
------------------------------------------------

def resp_op [Group G] [Group H] (φ : G → H) : Prop :=
  ∀ (a b : G), φ (a ⋆ b) = (φ a) ⋆ (φ b)
notation:65 φ:65 " respeita op" => resp_op φ

def resp_id [Group G] [Group H] (φ : G → H) : Prop :=
  φ (e : G) = (e : H)
notation:65 φ:65 " respeita id" => resp_id φ

def resp_inv [Group G] [Group H] (φ : G → H) : Prop :=
  ∀ (a : G), φ a⁻¹ = (φ a)⁻¹
notation:65 φ:65 " respeita inv" => resp_inv φ

def Group_homomorfismo [Group G] [Group H] (φ : G → H) : Prop :=
  φ respeita op ∧ φ respeita id ∧ φ respeita inv
notation:65 φ:65 " G-homo" => Group_homomorfismo φ

def Group_isomorfismo [Group G] [Group H] (φ : G → H) : Prop :=
  φ G-homo ∧ ∃ (ψ : H → G), ψ G-homo ∧ ψ ∘ φ = id ∧ φ ∘ ψ = id
notation:65 φ:65 " G-iso" => Group_isomorfismo φ
