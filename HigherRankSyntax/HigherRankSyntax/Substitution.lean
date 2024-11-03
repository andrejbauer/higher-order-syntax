import HigherRankSyntax.Syntax
import HigherRankSyntax.Renaming

def Substitution γ δ := ∀ {{α}}, Var α γ → Arg δ α
infix:25 " →ˢ " => Substitution

namespace Substitution

def eta {γ} : γ →ˢ γ :=
  fun {α} x => x.varLeft ◃ (fun {β} (y : Var β α) => ⟦ Var.varRight ⇑ʳ _ ⟧ʳ (eta y))
termination_by γ.rank
decreasing_by apply rank_Var_lt ; assumption

def lift {γ δ} (f : γ →ʳ δ) : γ →ˢ δ :=
  fun {_} x => eta (f x)

/- However, it looks like in practice it does terminate -/
#check @eta (⟦ 𝟘 ⟧ ⊕ ⟦ 𝟘 ⟧) _ Var.varHere.varLeft
#check @eta (⟦ 𝟘 ⟧ ⊕ ⟦ 𝟘 ⟧) _ Var.varHere.varRight
#check @eta (⟦ ⟦ 𝟘 ⟧ ⊕ ⟦ 𝟘 ⟧ ⟧) _ Var.varHere
#check @eta (⟦ ⟦ ⟦ 𝟘 ⟧ ⊕ ⟦ 𝟘 ⟧ ⟧ ⟧) _ Var.varHere

def extend {γ δ} (u : γ →ˢ δ) η : γ ⊕ η →ˢ δ ⊕ η
| _, .varLeft x => ⟦ Var.varLeft ⇑ʳ _ ⟧ʳ (u x)
| _, .varRight y => eta y.varRight

infixl:95 " ⇑ˢ " => Substitution.extend

@[reducible]
def opluss (γ : Shape) : List Shape → Shape
| [] => γ
| δ :: δs => opluss γ δs ⊕ δ

infixl:30 " ⊕⊕ " => Substitution.opluss

@[reducible]
def Renaming.sum {γ δ θ} (f : γ →ʳ θ) (g : δ →ʳ θ) : γ ⊕ δ →ʳ θ
| _, .varLeft x => f x
| _, .varRight x => g x

infix:30 " ⊕ʳ " => Renaming.sum

@[reducible]
def assocLeft {γ δ θ} : γ ⊕ (δ ⊕ θ) →ʳ (γ ⊕ δ) ⊕ θ :=
  (.varLeft ∘ʳ .varLeft) ⊕ʳ ((.varLeft ∘ʳ .varRight) ⊕ʳ .varRight)

@[reducible]
def assocRight {γ δ θ} : (γ ⊕ δ) ⊕ θ →ʳ γ ⊕ (δ ⊕ θ) :=
  (.varLeft ⊕ʳ (.varRight ∘ʳ .varLeft)) ⊕ʳ (.varRight ∘ʳ .varRight)

lemma reassocLR {γ δ θ} : @assocLeft γ δ θ ∘ʳ @assocRight γ δ θ = 𝟙ʳ := by
  funext α x
  obtain (_|(_|_)) := x <;> rfl

lemma reassocRL {γ δ θ} : @assocRight γ δ θ ∘ʳ @assocLeft γ δ θ = 𝟙ʳ := by
  funext α x
  -- why doesn't the symmetric obtain work here? obtain ((_|_)|_) := x <;> rfl
  cases x
  · rfl
  · case h.h.varRight z =>
    cases z
    · rfl
    · rfl

-- def act' {δ α : Shape} (u : α →ˢ δ) : ∀ βs, Expr ((δ ⊕ α) ⊕⊕ βs) → Expr (δ ⊕⊕ βs)
-- | [], .varLeft x ◃ ts => x ◃ (fun ⦃β⦄ z => act' u [β] (ts z))
-- | [], .varRight y ◃ ts => act' (fun ⦃β⦄ z => act' u [β] (ts z)) [] (u y)
-- | β :: βs, .varLeft x ◃ ts => _
-- | β :: βs, .varRight y ◃ ts => .varRight y ◃ (fun ⦃β'⦄ z => act' u (β' :: β :: βs) (ts z))

def act' {α β γ : Shape} (u : β →ˢ α) : Expr ((α ⊕ β) ⊕ γ) → Expr (α ⊕ γ)
  | .varLeft (.varLeft x) ◃ ts => .varLeft x ◃ (fun ⦃δ⦄ z => ⟦ assocLeft ⟧ʳ act' u (⟦ assocRight ⟧ʳ ts z))
  | .varLeft (.varRight y) ◃ ts => have A := u y ; sorry
  | .varRight z ◃ ts => .varRight z ◃ (fun ⦃_⦄ z =>  ⟦ assocLeft ⟧ʳ act' u (⟦ assocRight ⟧ʳ ts z))


def act {γ δ} (u : γ →ˢ δ) : Expr γ → Expr δ
  | x ◃ ts => act' (fun ⦃β⦄ y => act (u ⇑ˢ β) (ts y)) [] (u x)

def comp {γ δ θ} (u : γ →ˢ δ) (v : δ →ˢ θ) : γ →ˢ θ
| β, x => act (v ⇑ˢ β) (u x)

notation:90 g:90 " ∘ˢ " f:91 => Substitution.comp f g

end Substitution
