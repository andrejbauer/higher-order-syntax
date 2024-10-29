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

-- mutual
--   def comp {γ δ η} (u : γ →ˢ δ) (v : δ →ˢ η) : γ →ˢ η :=
--   fun {α} x => act (v ⇑ˢ α) (u x)

--   def dog {δ α β'} (u : α →ˢ δ) : Expr ((δ ⊕ α) ⊕ β') → Expr (δ ⊕ β')
--   | .varLeft (.varRight x) ◃ ts => let A := u x; _
--   | .varLeft (.varLeft y) ◃ ts => sorry
--   | .varRight z ◃ ts => sorry

--   def cow {δ α} (u : α →ˢ δ) : Expr (δ ⊕ α) → Expr δ
--   | .varLeft x ◃ ts => x ◃ (fun {β} y => sorry)
--   | .varRight y ◃ ts => cow (fun {β'} y => dog u (ts y)) (u y)

--   def act {γ δ} (u : γ →ˢ δ) : Expr γ → Expr δ
--   | x ◃ ts => cow (comp ts u) (u x)
-- end

notation:90 g:90 " ∘ʳ " f:90 => Renaming.comp f g

end Substitution
