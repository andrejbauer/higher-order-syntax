import HigherRankSyntax.Syntax
import HigherRankSyntax.Renaming

def Substitution γ δ := ∀ {{α}}, Var α γ → Expr (δ ⊕ α)
infix:25 " →ˢ " => Substitution

namespace Substitution

/-- The identity substutition -/
def id {γ} : γ →ˢ γ :=
  fun {α} x => x.varLeft ◃ (fun {β} (y : Var β α) => ⟦ Var.varRight ⇑ʳ _ ⟧ʳ (id y))
termination_by γ.rank
decreasing_by apply rank_Var_lt ; assumption

@[inherit_doc]
notation " 𝟙ˢ " => Substitution.id

/-- Lift a renaming to a substitution -/
def lift {γ δ} (f : γ →ʳ δ) : γ →ˢ δ :=
  fun {_} x => 𝟙ˢ (f x)

/-- Extend a substutution on the right. This is generally used when
    a substitution needs to be used under a binder. -/
def extend {γ δ} (u : γ →ˢ δ) η : γ ⊕ η →ˢ δ ⊕ η
| _, .varLeft x => ⟦ Var.varLeft ⇑ʳ _ ⟧ʳ (u x)
| _, .varRight y => 𝟙ˢ y.varRight

@[inherit_doc]
infixl:95 " ⇑ˢ " => Substitution.extend

/-- Compose a renaming and a substutition. -/
def renaming_comp {α β γ} (f : β →ʳ γ) (u : α →ˢ β) : α →ˢ γ :=
  fun ⦃δ⦄ x => ⟦ f ⇑ʳ δ ⟧ʳ u x

@[inherit_doc]
infixr:95 " ʳ∘ˢ " => Substitution.renaming_comp

/-- Compose a substitution and a renaming -/
def comp_renaming {α β γ} (u : β →ˢ γ) (f : α →ʳ β) : α →ˢ γ :=
  fun ⦃_⦄ x => u (f x)

@[inherit_doc]
infixr:95 " ˢ∘ʳ " => Substitution.comp_renaming

/-- Sum of substitutions -/
def sum {α β γ} (u : α →ˢ γ) (v : β →ˢ γ) : α ⊕ β →ˢ γ
| _, .varLeft x => u x
| _, .varRight y => v y

@[inherit_doc]
infix:30 " ⊕ˢ " => Substitution.sum

mutual

  def actS {α β γ δ : Shape} (u : β →ˢ α ⊕ γ) : Expr ((α ⊕ β) ⊕ δ) → Expr ((α ⊕ γ) ⊕ δ)
    | .varLeft (@Var.varLeft _ _ δ x) ◃ ts => .varLeft (.varLeft x) ◃ (fun ⦃θ⦄ (y : Var θ δ) => ⟦ .assocLeft ⟧ʳ actS u (⟦ .assocRight ⟧ʳ ts y))
    | .varLeft (@Var.varRight _ _ δ x) ◃ ts =>
      ⟦ .cancelZeroRight ⟧ʳ actS (fun ⦃_⦄ y => ⟦ .assocLeft ⟧ʳ actS u (⟦ .assocRight ⟧ʳ ts y)) (⟦ @Var.varLeft _ 𝟘 ⟧ʳ u x)
    | .varRight x ◃ ts => .varRight x ◃ (fun ⦃δ⦄ y =>  ⟦ .assocLeft ⟧ʳ actS u (⟦ .assocRight ⟧ʳ ts y))
  termination_by e => (β.rank, Expr.sizeOf e)
  decreasing_by
  · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg
  · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg
  · apply Prod.Lex.left
    apply rank_Var_lt x
  · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg

  def act' {α β γ : Shape} (u : β →ˢ α) (e : Expr ((α ⊕ β) ⊕ γ)) : Expr (α ⊕ γ) :=
    ⟦ .cancelZeroRight ⇑ʳ γ ⟧ʳ @actS α β 𝟘 γ (fun θ y => ⟦ Var.varLeft ⇑ʳ θ ⟧ʳ u y) e

end

def act {γ δ} (u : γ →ˢ δ) : Expr γ → Expr δ
  | x ◃ ts => ⟦ .cancelZeroRight ⟧ʳ (act' (fun ⦃β⦄ y => act (u ⇑ˢ β) (ts y)) (⟦ .insertZeroRight ⟧ʳ u x))

/-- Composition of substitutions -/
def comp {γ δ θ} (u : γ →ˢ δ) (v : δ →ˢ θ) : γ →ˢ θ
| β, x => act (v ⇑ˢ β) (u x)

@[inherit_doc]
notation:90 g:90 " ∘ˢ " f:91 => Substitution.comp f g

end Substitution
