import HigherRankSyntax.Syntax

def Expr.substitution (γ δ : Shape) := ∀ {α}, Var α γ → Expr (δ ⊕ α)

infix:50 " →ˢ " => Expr.substitution
