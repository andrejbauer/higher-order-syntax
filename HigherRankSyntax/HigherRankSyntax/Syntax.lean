
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
| γ ⊕ δ => max (rank γ) (rank δ)

/-- Variables of given arity in a given shape -/
inductive Var : Arity → Shape → Type where
| varHere : ∀ {α : Arity}, Var α ⟦ α ⟧
| varLeft : ∀ {γ δ} {{α}}, Var α γ → Var α (γ ⊕ δ)
| varRight : ∀ {γ δ} {{α}}, Var α δ → Var α (γ ⊕ δ)

/-- Fold on all variables in a given shape -/
def Shape.fold.{u} (γ : Shape) {A : Type u} (a : A) (f : A → ∀ ⦃α⦄, Var α γ → A) : A :=
  match γ with
  | 𝟘 => a
  | ⟦ _ ⟧ => f a .varHere
  | γ₁ ⊕ γ₂ => γ₂.fold (γ₁.fold a (fun b _ x => f b x.varLeft)) (fun b _ x => f b x.varRight)

theorem rank_Var_lt {α γ} (x : Var α γ) : α.rank < γ.rank := by
  induction x
  case varHere => simp
  case varLeft δ β α _ _ =>
    simp [Shape.rank]
    calc
      α.rank < δ.rank := by assumption
           _ ≤ max δ.rank β.rank := by exact Nat.le_max_left δ.rank β.rank
  case varRight δ β α _ _ =>
    simp [Shape.rank]
    calc
      α.rank < β.rank := by assumption
           _ ≤ max δ.rank β.rank := by exact Nat.le_max_right δ.rank β.rank

inductive Expr : Shape → Type where
| apply : ∀ {α γ}, Var α γ → (∀ {{β}}, Var β α → Expr (γ ⊕ β)) → Expr γ

infix:80 " ◃ " => Expr.apply

@[reducible]
def Expr.sizeOf {γ} : Expr γ → Nat
| @Expr.apply α _ _ ts => 1 + α.fold 0 (fun n _ y => n + (ts y).sizeOf)

theorem Expr.sizeOfArg {α γ} (x : Var α γ) (ts : ∀ {{β}}, Var β α → Expr (γ ⊕ β)) {δ} (y : Var δ α) :
  (ts y).sizeOf < (x ◃ ts).sizeOf := by
  induction γ
  · cases x
  · sorry
  · sorry

instance {γ} : SizeOf (Expr γ) where sizeOf := Expr.sizeOf
