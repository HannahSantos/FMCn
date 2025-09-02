import FMCn.IEA.Semigroup.Definitions

class MonoidM (α : Type u) extends SemigroupM α where
  e : α
  id_opm : ∀ (a : α), e ⋆ a = a
  opm_id : ∀ (a : α), a ⋆ e = a
open MonoidM

def idMM [MonoidM M] (x : M) : Prop :=
  (∀ (a : M), a ⋆ x = a) ∧ ∀ (b : M), x ⋆ b = b
notation:65 x:65 " is_(⋆)-id" => idMM x

------------------------------------------------
-- Pows Multiplicativos :
------------------------------------------------

def PowM_R [MonoidM M] : M → Nat → M
  | _, 0 => e
  | a, .succ n => a ⋆ (PowM_R a n)
notation:65 lhs:65 " ↑ᴿ " rhs:66 => PowM_R lhs rhs

def PowM_L [MonoidM M] : Nat → M → M
  | 0, _ => e
  | .succ n, a => (PowM_L n a) ⋆ a
notation:65 lhs:65 " ↑ᴸ " rhs:66 => PowM_L rhs lhs

-------------------------------------------------

class MonoidA (α : Type u) extends SemigroupA α where
  z : α
  id_opa : ∀ (a : α), z ⊹ a = a
  opa_id : ∀ (a : α), a ⊹ z = a
open MonoidA

def idMA [MonoidA M] (x : M) : Prop :=
  (∀ (a : M), a ⊹ x = a) ∧ ∀ (b : M), x ⊹ b = b
notation:65 x:65 " is_(⊹)-id" => idMA x

------------------------------------------------
-- Pows Aditivos :
------------------------------------------------

def PowA_R [MonoidA M] : M → Nat → M
  | _, 0 => z
  | a, .succ n => a ⊹ (PowA_R a n)
notation:65 lhs:65 " ^ᴿ " rhs:66 => PowA_R lhs rhs

def PowA_L [MonoidA M] : Nat → M → M
  | 0, _ => z
  | .succ n, a => (PowA_L n a) ⊹ a
notation:65 lhs:65 " ^ᴸ " rhs:66 => PowA_L rhs lhs
