import HigherRankedSyntax.Syntax

def Expr.substitution (γ δ : Shape) := ∀ {α}, α ε γ → Expr (δ ⊕ α)

infix:50 " →ˢ " => Expr.substitution
