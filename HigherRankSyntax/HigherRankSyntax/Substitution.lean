import HigherRankSyntax.Syntax
import HigherRankSyntax.Renaming

def Substitution γ δ := ∀ {α}, Var α γ → Arg δ α
infix:25 " →ˢ " => Substitution

namespace Substitution

/- At the moment this is still unsafe, as Lean does not see why recursion terminates. -/
unsafe def id {{γ}} : γ →ˢ γ :=
  fun {α} x => x.varLeft ◃ (fun {β} (y : Var β α) => ⟦ (fun {_} z => z.varRight) ⇑ʳ β ⟧ʳ (id y))

/- However, it looks like in practice it does terminate -/
#check @id (⟦ 𝟘 ⟧ ⊕ ⟦ 𝟘 ⟧) _ Var.varHere.varLeft
#check @id (⟦ 𝟘 ⟧ ⊕ ⟦ 𝟘 ⟧) _ Var.varHere.varRight
#check @id (⟦ ⟦ 𝟘 ⟧ ⊕ ⟦ 𝟘 ⟧ ⟧) _ Var.varHere
#check @id (⟦ ⟦ ⟦ 𝟘 ⟧ ⊕ ⟦ 𝟘 ⟧ ⟧ ⟧) _ Var.varHere


end Substitution
