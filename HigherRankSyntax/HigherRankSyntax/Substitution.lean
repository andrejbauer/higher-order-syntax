import HigherRankSyntax.Syntax
import HigherRankSyntax.Renaming

def Substitution γ δ := ∀ {{α}}, Var α γ → Expr (δ ⊕ α)
infix:25 " →ˢ " => Substitution

namespace Substitution

def id {γ} : γ →ˢ γ :=
  fun {α} x => x.varLeft ◃ (fun {β} (y : Var β α) => ⟦ Var.varRight ⇑ʳ _ ⟧ʳ (id y))
termination_by γ.rank
decreasing_by apply rank_Var_lt ; assumption

notation " 𝟙ˢ " => Substitution.id

def lift {γ δ} (f : γ →ʳ δ) : γ →ˢ δ :=
  fun {_} x => 𝟙ˢ (f x)

#check @id (⟦ 𝟘 ⟧ ⊕ ⟦ 𝟘 ⟧) _ Var.varHere.varLeft
#check @id (⟦ 𝟘 ⟧ ⊕ ⟦ 𝟘 ⟧) _ Var.varHere.varRight
#check @id (⟦ ⟦ 𝟘 ⟧ ⊕ ⟦ 𝟘 ⟧ ⟧) _ Var.varHere
#check @id (⟦ ⟦ ⟦ 𝟘 ⟧ ⊕ ⟦ 𝟘 ⟧ ⟧ ⟧) _ Var.varHere

def extend {γ δ} (u : γ →ˢ δ) η : γ ⊕ η →ˢ δ ⊕ η
| _, .varLeft x => ⟦ Var.varLeft ⇑ʳ _ ⟧ʳ (u x)
| _, .varRight y => 𝟙ˢ y.varRight

infixl:95 " ⇑ˢ " => Substitution.extend

@[reducible]
def opluss (γ : Shape) : List Shape → Shape
| [] => γ
| δ :: δs => opluss γ δs ⊕ δ

infixl:30 " ⊕⊕ " => Substitution.opluss

@[reducible]
def Renaming.sum {γ δ θ} (f : γ →ʳ θ) (g : δ →ʳ θ) : γ ⊕ δ →ʳ θ
| _, .varLeft x => f x
| _, .varRight x => g x

infix:30 " ⊕ʳ " => Renaming.sum

@[reducible]
def assocLeft {γ δ θ} : γ ⊕ (δ ⊕ θ) →ʳ (γ ⊕ δ) ⊕ θ :=
  (.varLeft ∘ʳ .varLeft) ⊕ʳ ((.varLeft ∘ʳ .varRight) ⊕ʳ .varRight)

@[reducible]
def assocRight {γ δ θ} : (γ ⊕ δ) ⊕ θ →ʳ γ ⊕ (δ ⊕ θ) :=
  (.varLeft ⊕ʳ (.varRight ∘ʳ .varLeft)) ⊕ʳ (.varRight ∘ʳ .varRight)

lemma reassocLR {γ δ θ} : @assocLeft γ δ θ ∘ʳ @assocRight γ δ θ = 𝟙ʳ := by
  funext α x
  obtain (_|(_|_)) := x <;> rfl

lemma reassocRL {γ δ θ} : @assocRight γ δ θ ∘ʳ @assocLeft γ δ θ = 𝟙ʳ := by
  funext α x
  -- why doesn't the symmetric obtain work here? obtain ((_|_)|_) := x <;> rfl
  cases x
  · rfl
  · case h.h.varRight z =>
    cases z
    · rfl
    · rfl

def unRight {γ} : γ ⊕ 𝟘 →ʳ γ
| _, .varLeft x => x

lemma unRightLeft {γ} : unRight ∘ʳ @Var.varLeft γ 𝟘 = 𝟙ʳ := by
  funext α x
  rfl

-- def act' {δ α : Shape} (u : α →ˢ δ) : ∀ βs, Expr ((δ ⊕ α) ⊕⊕ βs) → Expr (δ ⊕⊕ βs)
-- | [], .varLeft x ◃ ts => x ◃ (fun ⦃β⦄ z => act' u [β] (ts z))
-- | [], .varRight y ◃ ts => act' (fun ⦃β⦄ z => act' u [β] (ts z)) [] (u y)
-- | β :: βs, .varLeft x ◃ ts => _
-- | β :: βs, .varRight y ◃ ts => .varRight y ◃ (fun ⦃β'⦄ z => act' u (β' :: β :: βs) (ts z))

def sum {α β γ} (u : α →ˢ γ) (v : β →ˢ γ) : α ⊕ β →ˢ γ
| _, .varLeft x => u x
| _, .varRight y => v y

infix:30 " ⊕ˢ " => Substitution.sum

def prepend {α β} (u : β →ˢ α) : α ⊕ β →ˢ α := 𝟙ˢ ⊕ˢ u

mutual

  def actS {α β γ δ : Shape} (u : β →ˢ α ⊕ γ) : Expr ((α ⊕ β) ⊕ δ) → Expr ((α ⊕ γ) ⊕ δ)
    | .varLeft (@Var.varLeft _ _ δ x) ◃ ts => .varLeft (.varLeft x) ◃ (fun ⦃θ⦄ (y : Var θ δ) => ⟦ assocLeft ⟧ʳ actS u (⟦ assocRight ⟧ʳ ts y))
    | .varLeft (@Var.varRight _ _ δ x) ◃ ts =>
      ⟦ unRight ⟧ʳ actS (fun ⦃_⦄ y => ⟦ assocLeft ⟧ʳ actS u (⟦ assocRight ⟧ʳ ts y)) (⟦ @Var.varLeft _ 𝟘 ⟧ʳ u x)
    | .varRight x ◃ ts => .varRight x ◃ (fun ⦃δ⦄ y =>  ⟦ assocLeft ⟧ʳ actS u (⟦ assocRight ⟧ʳ ts y))
  termination_by e => (β.rank, Expr.sizeOf e)
  decreasing_by
  · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg
  · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg
  · apply Prod.Lex.left
    apply rank_Var_lt x
  · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg

  def act' {α β γ : Shape} (u : β →ˢ α) : Expr ((α ⊕ β) ⊕ γ) → Expr (α ⊕ γ)
    | .varLeft (@Var.varLeft _ _ δ x) ◃ ts => .varLeft x ◃ (fun ⦃θ⦄ (y : Var θ δ) => ⟦ assocLeft ⟧ʳ act' u (⟦ assocRight ⟧ʳ ts y))
    | .varLeft (@Var.varRight _ _ δ x) ◃ ts => ⟦ unRight ⟧ʳ actS (fun ⦃_⦄ y => ⟦ assocLeft ⟧ʳ act' u (⟦ assocRight ⟧ʳ ts y)) (⟦ @Var.varLeft _ 𝟘 ⟧ʳ u x)
    | .varRight x ◃ ts => .varRight x ◃ (fun ⦃δ⦄ y =>  ⟦ assocLeft ⟧ʳ act' u (⟦ assocRight ⟧ʳ ts y))
  termination_by e => Expr.sizeOf e
  decreasing_by
  · rw [Renaming.eq_size] ; apply Expr.sizeOfArg
  · rw [Renaming.eq_size] ; apply Expr.sizeOfArg
  · rw [Renaming.eq_size] ; apply Expr.sizeOfArg

end

def act {γ δ} (u : γ →ˢ δ) : Expr γ → Expr δ
  | x ◃ ts => ⟦ unRight ⟧ʳ (act' (fun ⦃β⦄ y => act (u ⇑ˢ β) (ts y)) (⟦ @Var.varLeft _ 𝟘 ⟧ʳ u x))

def comp {γ δ θ} (u : γ →ˢ δ) (v : δ →ˢ θ) : γ →ˢ θ
| β, x => act (v ⇑ˢ β) (u x)

notation:90 g:90 " ∘ˢ " f:91 => Substitution.comp f g

end Substitution
