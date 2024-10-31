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

def act' {δ α : Shape} (u : α →ˢ δ) : ∀ βs, Expr ((δ ⊕ α) ⊕⊕ βs) → Expr (δ ⊕⊕ βs)
| [], .varLeft x ◃ ts => x ◃ (fun ⦃β⦄ z => act' u [β] (ts z))
| [], .varRight y ◃ ts => act' (fun ⦃β⦄ z => act' u [β] (ts z)) [] (u y)
| β :: βs, .varLeft x ◃ ts => _
| β :: βs, .varRight y ◃ ts => .varRight y ◃ (fun ⦃β'⦄ z => act' u (β' :: β :: βs) (ts z))

def act {γ δ} (u : γ →ˢ δ) : Expr γ → Expr δ
  | x ◃ ts => act' (fun ⦃β⦄ y => act (u ⇑ˢ β) (ts y)) [] (u x)

def comp {γ δ θ} (u : γ →ˢ δ) (v : δ →ˢ θ) : γ →ˢ θ
| β, x => act (v ⇑ˢ β) (u x)

notation:90 g:90 " ∘ˢ " f:90 => Substitution.comp f g

end Substitution
