import FMCn.IEA.Monoid.Definitions

class Mul_Inv (α : Type u) where minv : α → α
postfix:max "⁻¹"  => Mul_Inv.minv
open Mul_Inv

class GroupM (α : Type u) extends MonoidM α, Mul_Inv α where
  minv_opm : ∀ (a : α), a⁻¹ ⋆ a = e
  opm_minv : ∀ (a : α), a ⋆ a⁻¹ = e
open MonoidM GroupM

def invGM [GroupM G] (x a : G): Prop :=
  x ⋆ a = e ∧ a ⋆ x = e
notation:65 a:65 " é o (⋆)-inverso de " b:66 => invGM a b

------------------------------------------------
-- GroupM-Homomorphisms :
------------------------------------------------

def resp_opm [GroupM G] [GroupM H] (φ : G → H) : Prop :=
  ∀ (a b : G), φ (a ⋆ b) = (φ a) ⋆ (φ b)
notation:65 φ:65 " respeita (⋆)" => resp_opm φ

def resp_idm [GroupM G] [GroupM H] (φ : G → H) : Prop :=
  φ (e : G) = (e : H)
notation:65 φ:65 " respeita 'e'" => resp_idm φ

def resp_invm [GroupM G] [GroupM H] (φ : G → H) : Prop :=
  ∀ (a : G), φ a⁻¹ = (φ a)⁻¹
notation:65 φ:65 " respeita (⁻¹)" => resp_invm φ

def GroupM_homomorfismo [GroupM G] [GroupM H] (φ : G → H) : Prop :=
  φ respeita (⋆) ∧ φ respeita 'e' ∧ φ respeita (⁻¹)
notation:65 φ:65 " G-Mhomo" => GroupM_homomorfismo φ

def GroupM_isomorfismo [GroupM G] [GroupM H] (φ : G → H) : Prop :=
  φ G-Mhomo ∧ ∃ (ψ : H → G), ψ G-Mhomo ∧ ψ ∘ φ = id ∧ φ ∘ ψ = id
notation:65 φ:65 " G-Miso" => GroupM_isomorfismo φ

---------------------------------------------------------------

class Add_Inv (α : Type u) where ainv : α → α
prefix:80 "−"  => Add_Inv.ainv
open Mul_Inv

class GroupA (α : Type u) extends MonoidA α, Add_Inv α where
  ainv_opa : ∀ (a : α), −a ⊹ a = z
  opa_ainv : ∀ (a : α), a ⊹ −a = z
open MonoidA GroupA

def invGA [GroupA G] (x a : G): Prop :=
  x ⊹ a = z ∧ a ⊹ x = z
notation:65 a:65 " é o (⊹)-inverso de " b:66 => invGA a b

------------------------------------------------
-- GroupA-Homomorphisms :
------------------------------------------------

def resp_opa [GroupA G] [GroupA H] (φ : G → H) : Prop :=
  ∀ (a b : G), φ (a ⊹ b) = (φ a) ⊹ (φ b)
notation:65 φ:65 " respeita (⊹)" => resp_opa φ

def resp_ida [GroupA G] [GroupA H] (φ : G → H) : Prop :=
  φ (z : G) = (z : H)
notation:65 φ:65 " respeita 'z'" => resp_ida φ

def resp_inva [GroupA G] [GroupA H] (φ : G → H) : Prop :=
  ∀ (a : G), φ (−a) = −(φ a)
notation:65 φ:65 " respeita (−)" => resp_inva φ

def GroupA_homomorfismo [GroupA G] [GroupA H] (φ : G → H) : Prop :=
  φ respeita (⊹) ∧ φ respeita 'z' ∧ φ respeita (−)
notation:65 φ:65 " G-Ahomo" => GroupA_homomorfismo φ

def GroupA_isomorfismo [GroupA G] [GroupA H] (φ : G → H) : Prop :=
  φ G-Ahomo ∧ ∃ (ψ : H → G), ψ G-Ahomo ∧ ψ ∘ φ = id ∧ φ ∘ ψ = id
notation:65 φ:65 " G-Aiso" => GroupA_isomorfismo φ
