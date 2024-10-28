
inductive Shape where
  /-- the empty shape -/
| empty : Shape
  /-- the shape containing precisely one item -/
| slot : Shape → Shape
  /-- juxtaposition of two shapes -/
| oplus : Shape → Shape → Shape
deriving Repr
-- TODO: implement better Repr instance for shapes

@[inherit_doc]
notation "𝟘" => Shape.empty

@[inherit_doc]
notation:max "⟦" e  "⟧" => Shape.slot e

@[inherit_doc]
notation (priority := default+1) γ:31 " ⊕ " δ:31 => Shape.oplus γ δ

abbrev Arity := Shape

def Shape.rank : Shape → Nat
| 𝟘 => 0
| ⟦ γ ⟧  => 1 + rank γ
| γ ⊕ δ => 1 + max (rank γ) (rank δ)

/-- Variables of given arity in a given shape -/
inductive Var : Arity → Shape → Type where
| varHere : ∀ {α : Arity}, Var α ⟦ α ⟧
| varLeft : ∀ {α γ δ}, Var α γ → Var α (γ ⊕ δ)
| varRight : ∀ {α γ δ}, Var α δ → Var α (γ ⊕ δ)

inductive Expr : Shape → Type where
| apply : ∀ {α γ}, Var α γ → (∀ {β}, Var β α → Expr (γ ⊕ β)) → Expr γ

abbrev Arg γ δ := Expr (γ ⊕ δ)

infix:80 " ◃ " => Expr.apply

def Substitution α γ := ∀ {β}, Var β α → Arg γ β

infix:25 " →ˢ " => Substitution
