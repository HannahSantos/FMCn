------------------------------------------------
-- Algebra :
------------------------------------------------

class has_Op (α : Type u) where op : α × α → α
notation:65 a:65 " ⋆ " b:66 => has_Op.op ⟨a, b⟩
open has_Op

class Semigroup (α : Type u) extends has_Op α where
  Op_Ass : ∀ (a b c : α), a ⋆ b ⋆ c = a ⋆ (b ⋆ c)
open Semigroup

class has_Id (α : Type u) where e : α
open has_Id

class Monoid (α : Type u) extends Semigroup α, has_Id α where
  Id_Op : ∀ (a : α), e ⋆ a = a
  Op_Id : ∀ (a : α), a ⋆ e = a
open Monoid

class has_Inv (α : Type u) where inv : α → α
postfix:max "⁻¹"  => has_Inv.inv
open has_Inv

class Group (α : Type u) extends Monoid α, has_Inv α where
  Op_Inv_L : ∀ (a : α), a⁻¹ ⋆ a = e
  Op_Inv_R : ∀ (a : α), a ⋆ a⁻¹ = e
open Group

def invG [Group G] (x a : G): Prop :=
  x ⋆ a = e ∧ a ⋆ x = e
notation:65 a:65 " é o inverso de " b:66 => invG a b

def idM [Monoid M] (x : M) : Prop :=
  (∀ (a : M), a ⋆ x = a) ∧ ∀ (b : M), x ⋆ b = b
notation:65 x:65 " é a identidade" => idM x

------------------------------------------------
-- Pows :
------------------------------------------------

def Pow_R [Monoid M] : M → Nat → M
  | _, 0 => e
  | a, .succ n => a ⋆ (Pow_R a n)
notation:65 lhs:65 " ↑ᴿ " rhs:66 => Pow_R lhs rhs

def Pow_L [Monoid M] : Nat → M → M
  | 0, _ => e
  | .succ n, a => (Pow_L n a) ⋆ a
notation:65 lhs:65 " ↑ᴸ " rhs:66 => Pow_L rhs lhs

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
