
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

@[reducible]
def Shape.rank : Shape → Nat
| 𝟘 => 0
| ⟦ γ ⟧  => 1 + rank γ
| γ ⊕ δ => 1 + max (rank γ) (rank δ)

/-- Variables of given arity in a given shape -/
inductive Var : Arity → Shape → Type where
| varHere : ∀ {α : Arity}, Var α ⟦ α ⟧
| varLeft : ∀ {α γ δ}, Var α γ → Var α (γ ⊕ δ)
| varRight : ∀ {α γ δ}, Var α δ → Var α (γ ⊕ δ)

theorem rank_Var_lt {α γ} (x : Var α γ) : α.rank < γ.rank := by
  induction x
  case varHere => simp
  case varLeft η δ β _ =>
    simp [Shape.rank]
    calc
      α.rank < η.rank := by assumption
           _ ≤ max η.rank δ.rank := by exact Nat.le_max_left η.rank δ.rank
           _ < 1 + max η.rank δ.rank := by refine Nat.lt_add_of_pos_left Nat.zero_lt_one
  case varRight η δ β _ =>
    simp [Shape.rank]
    calc
      α.rank < δ.rank := by assumption
           _ ≤ max η.rank δ.rank := by exact Nat.le_max_right η.rank δ.rank
           _ < 1 + max η.rank δ.rank := by refine Nat.lt_add_of_pos_left Nat.zero_lt_one

inductive Expr : Shape → Type where
| apply : ∀ {α γ}, Var α γ → (∀ {β}, Var β α → Expr (γ ⊕ β)) → Expr γ

abbrev Arg γ δ := Expr (γ ⊕ δ)

infix:80 " ◃ " => Expr.apply
