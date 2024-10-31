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

def subst_bound {δ α} (u : α →ˢ δ) : δ ⊕ α →ˢ δ
| _, .varLeft x => eta x
| _, .varRight x => u x

mutual
  def extendMany {γ δ} (u : γ →ˢ δ) : ∀ (ηs : List Shape), γ ⊕⊕ ηs →ˢ δ ⊕⊕ ηs
    | [], _, x => u x
    | _ :: ηs, α, .varLeft x => ⟦ .varLeft ⇑ʳ α ⟧ʳ (extendMany u ηs x)
    | _ :: ηs, _, .varRight x => eta x.varRight

  def act_unbound {γ δ} (u : γ →ˢ δ) : ∀ (ηs : List Shape), Expr (γ ⊕⊕ ηs) → Expr (δ ⊕⊕ ηs)
  | [], e => act u e
  | η :: ηs, .varLeft x ◃ ts => _
  | η :: ηs, .varRight x ◃ ts => _

  def act_bound {γ α} (u : α →ˢ γ) : Expr (γ ⊕ α) → Expr γ
  | .varLeft x ◃ ts => x ◃ ts
  | .varRight x ◃ ts => u x

  def act {γ δ} (u : γ →ˢ δ) : Expr γ → Expr δ
    | x ◃ ts => act_bound (fun ⦃β⦄ y => act_unbound u [β] (ts y)) (u x)
end




notation:90 g:90 " ∘ʳ " f:90 => Renaming.comp f g

end Substitution
