variable {α α' β β' γ δ : Type}

namespace data

notation:max "𝟘" => Empty
notation:max "𝟙" => Unit

def id : α → α
  | x => x

def outl : α × β → α
  | ⟨a, _⟩ => a

def outr : α × β → β
  | ⟨_, b⟩ => b

def prod_fun : (α → γ) → (β → δ) → α × β → γ × δ
  | f, g, ⟨a, b⟩ => ⟨f a, g b⟩
infix:80 " × " => prod_fun

def pairing : (δ → α) → (δ → β) → δ → α × β
  | f, g, d => ⟨f d, g d⟩
notation "⟪" f ", " g "⟫" => pairing f g

def copairing : (α → γ) → (β → δ) → α ⊕ β → γ ⊕ δ
  | f, _, .inl x => .inl (f x)
  | _, g, .inr x => .inr (g x)
infix:80 " ⊕ " => copairing

def comp : (β → γ) → (α → β) → α → γ
  | f, g, a => f (g a)
infixr:75 " ⋄ " => comp

def Fun_to_fun : (α' → α) → (β → β') → (α → β) → α' → β'
  | f, g, h => g ⋄ h ⋄ f

def Δ : α → α × α
  | a => ⟨a, a⟩

def Prod_Pow_to_Sum {α β δ : Type}: (α → δ) × (β → δ) → α ⊕ β → δ
  | w => (fun x => match x with
                    | .inl a => w.1 a
                    | .inr b => w.2 b)

def Pow_Sum_to_Prod {α β δ : Type}: (α ⊕ β → δ) → (α → δ) × (β → δ)
  | f => ⟨fun x => f (.inl x), fun y => f (.inr y)⟩

def curry : (α × β → δ) → α → β → δ
  | f => fun a => fun b => f ⟨a, b⟩

def uncurry : (α → β → δ) → α × β → δ
  | f => fun ⟨a, b⟩ => f a b

def Pow_one {α : Type} : (𝟙 → α) → α
  | f => f ()

def Pow_one_back {α : Type}: α → 𝟙 → α
  | a => fun () => a

def Pow_two {α : Type} : (𝟙 ⊕ 𝟙 → α) → α × α
  | f => ⟨f (.inl ()), f (.inr ())⟩

def Two_pow {α : Type} : α × α → 𝟙 ⊕ 𝟙 → α
  | ⟨a, a'⟩ => fun x => (match x with
                    | .inl _ => a
                    | .inr _ => a')

def One_pow {α : Type} : (α → 𝟙) → 𝟙
  | _ => ()

def One_pow_back {α : Type} : 𝟙 → α → 𝟙
  | _ => fun _ => ()

def Distr (α β δ : Type) : δ × (α ⊕ β) → (δ × α) ⊕ (δ × β)
  | ⟨d, .inl a⟩ => .inl ⟨d, a⟩
  | ⟨d, .inr b⟩ => .inr ⟨d, b⟩

def Distr_back {α β δ : Type} : (δ × α) ⊕ (δ × β) → δ × (α ⊕ β)
  | .inl ⟨d, a⟩ => ⟨d, .inl a⟩
  | .inr ⟨d, b⟩ => ⟨d, .inr b⟩

def Ass_sum_one {α β γ : Type} : α ⊕ β ⊕ γ → (α ⊕ β) ⊕ γ
  | .inl a => .inl (.inl a)
  | .inr (.inl b) => .inl (.inr b)
  | .inr (.inr c) => .inr c

def Ass_sum_two {α β γ : Type} : (α ⊕ β) ⊕ γ → α ⊕ β ⊕ γ
  | .inl (.inl a) => .inl a
  | .inl (.inr b) => .inr (.inl b)
  | .inr c => .inr (.inr c)

def Com_sum {α β : Type} : α ⊕ β → β ⊕ α
  | .inl a => .inr a
  | .inr b => .inl b

def Id_sum {α : Type}: α ⊕ 𝟘 → α
  | .inl x => x

def Sum_id {α : Type}: α → α ⊕ 𝟘
  | x => .inl x

def Ass_prod_one { α β γ : Type} : (α × β) × γ → α × β × γ
  | ⟨⟨a, b⟩, c⟩ => ⟨a, ⟨b, c⟩⟩

def Ass_prod_two {α β γ : Type} : α × β × γ → (α × β) × γ
  | ⟨a, ⟨b, c⟩⟩ => ⟨⟨a, b⟩, c⟩

def Com_prod {α β : Type} : α × β → β × α
  | ⟨a, b⟩ => ⟨b, a⟩

def Id_prod {α : Type} : α × 𝟙 → α
  | ⟨a, ()⟩ => a

def id_prod {α : Type} : 𝟙 × α → α
  := Id_prod ⋄ Com_prod

def Prod_id {α : Type} : α → α × 𝟙
  | a => ⟨a, ()⟩
