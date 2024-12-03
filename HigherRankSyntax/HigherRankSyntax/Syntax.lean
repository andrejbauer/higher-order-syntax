
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
notation (priority := default+1) γ:31 " ⊕ " δ:31 => Shape.oplus γ δ

/-- A synonym for a shape, used when we think of a shape as specifying
    the arity of a variable. -/
def Arity := Shape

/-- The rank of a shape is the level of nesting of the slots -/
@[reducible]
def Shape.rank : Shape → Nat
| 𝟘 => 0
| .slot γ  => 1 + rank γ
| γ ⊕ δ => max (rank γ) (rank δ)

/-- Variables of given arity in a given shape -/
inductive Var : Arity → Shape → Type where
| varHere : ∀ {α : Arity}, Var α α.slot
| varLeft : ∀ {γ δ} {{α}}, Var α γ → Var α (γ ⊕ δ)
| varRight : ∀ {γ δ} {{α}}, Var α δ → Var α (γ ⊕ δ)

/-- Fold on all variables in a given shape -/
def Shape.fold.{u} (γ : Shape) {A : Type u} (a : A) (f : A → ∀ ⦃α⦄, Var α γ → A) : A :=
  match γ with
  | 𝟘 => a
  | .slot _ => f a .varHere
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

/-- Expressions over a given shape -/
inductive Expr : Shape → Type where
/-- Apply a variable to arguments -/
| apply : ∀ {α γ}, Var α γ → (∀ {{β}}, Var β α → Expr (γ ⊕ β)) → Expr γ

@[inherit_doc]
infix:80 " ◃ " => Expr.apply

@[reducible]
def Expr.sizeOf {γ} : Expr γ → Nat
| @Expr.apply α _ _ ts => 1 + α.fold 0 (fun n _ y => n + (ts y).sizeOf)

theorem Expr.sizeOfArg {α γ} (x : Var α γ) (ts : ∀ {{β}}, Var β α → Expr (γ ⊕ β)) {δ} (y : Var δ α) :
  (ts y).sizeOf < (x ◃ ts).sizeOf := sorry

instance {γ} : SizeOf (Expr γ) where sizeOf := Expr.sizeOf
