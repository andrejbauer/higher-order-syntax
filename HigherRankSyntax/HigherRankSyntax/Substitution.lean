
import HigherRankSyntax.Syntax
import HigherRankSyntax.Renaming

def Substitution γ δ := ∀ {{α}}, Var α γ → Expr (δ ⊕ α)
infix:25 " →ˢ " => Substitution

namespace Substitution

/-- The identity substutition -/
def id {γ} : γ →ˢ γ :=
  fun {α} x => x.varLeft ◃ (fun {β} (y : Var β α) => ⟦ Var.varRight ʳ⇑ _ ⟧ʳ (id y))
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
| _, .varLeft x => ⟦ Var.varLeft ʳ⇑ _ ⟧ʳ (u x)
| _, .varRight y => 𝟙ˢ y.varRight

@[inherit_doc]
infixl:95 " ⇑ˢ " => Substitution.extend

/-- Compose a renaming and a substutition. -/
def renaming_comp {α β γ} (f : β →ʳ γ) (u : α →ˢ β) : α →ˢ γ :=
  fun ⦃δ⦄ x => ⟦ f ʳ⇑ δ ⟧ʳ u x

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

def inst' {α β γ} (u : β →ˢ α ⊕ γ): Expr (α ⊕ β) → Expr (α ⊕ γ)
| .varLeft x ◃ ts => .varLeft x ◃ (fun ⦃_⦄ y => act' u (ts y))
| .varRight x ◃ ts => inst' (lift .varRight ⊕ˢ (fun ⦃_⦄ y => act' u (ts y))) (⟦ .assocRight ⟧ʳ u x)
termination_by e => (β.rank, Expr.sizeOf e)
decreasing_by
· sorry
· sorry
· sorry

-- ⟦ .cancelZeroRight ⟧ʳ act' (fun ⦃_⦄ y => ⟦ .assocLeft ⟧ʳ act' u (⟦ .assocRight ⟧ʳ ts y))
/-- The action of a substitution on an expression that is identity on a left and right part of a shape. -/
def act' {α β γ δ : Shape} (u : β →ˢ α ⊕ γ) : Expr ((α ⊕ β) ⊕ δ) → Expr ((α ⊕ γ) ⊕ δ)
  | .varLeft (.varLeft x) ◃ ts   =>  .varLeft (.varLeft x) ◃ (fun ⦃_⦄ y => ⟦ .assocLeft ⟧ʳ act' u (⟦ .assocRight ⟧ʳ ts y))
  | .varLeft (.varRight x) ◃ ts  =>  inst' (fun ⦃_⦄ y => ⟦ .assocLeft ⟧ʳ act' u (⟦ .assocRight ⟧ʳ ts y)) (u x)
  | .varRight x ◃ ts             =>  .varRight x ◃ (fun ⦃_⦄ y => ⟦ .assocLeft ⟧ʳ act' u (⟦ .assocRight ⟧ʳ ts y))
termination_by e => (β.rank, Expr.sizeOf e)
decreasing_by
· apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg
· apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg
· apply Prod.Lex.left
  apply rank_Var_lt x
· apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg

end

/-- The action of a substitution on an expression -/
def act.I {γ δ} (u : γ →ˢ δ) (e : Expr γ) : Expr δ := ⟦ .cancelZeroLeft ⟧ʳ inst' (.varRight ʳ∘ˢ u) (⟦ .insertZeroLeft ⟧ʳ e)

/-- The action of a substitution on an expression -/
def act.II {γ δ} (u : γ →ˢ δ) : Expr γ → Expr δ
  | x ◃ ts => ⟦ .cancelZeroRight ⟧ʳ (inst' (fun ⦃_⦄ y => ⟦ .insertZeroRightʳ⇑ _ ⟧ʳ act.II (u ⇑ˢ _) (ts y)) (u x))

/-- The action of a substitution on an expression -/
def act.III {γ δ} (u : γ →ˢ δ) : Expr γ → Expr δ
  | x ◃ ts =>
    ⟦ .cancelZeroRight ⟧ʳ (
      ⟦ (.cancelZeroRight ʳ⇑ 𝟘) ⟧ʳ
        act'
          (fun ⦃_⦄ y => ⟦ .insertZeroRightʳ⇑ _ ⟧ʳ act.III (u ⇑ˢ _) (ts y))
          (⟦ .insertZeroRight ⟧ʳ u x))

@[inherit_doc]
notation:60 " ⟦" u "⟧ˢ " e:61 => Substitution.act u e

/-- Composition of substitutions -/
def comp {γ δ θ} (u : γ →ˢ δ) (v : δ →ˢ θ) : γ →ˢ θ
| β, x => act (v ⇑ˢ β) (u x)

@[inherit_doc]
notation:90 g:90 " ∘ˢ " f:91 => Substitution.comp f g

/-- The extension of identity is identity -/
def extend_id (γ δ) : @id γ ⇑ˢ δ = 𝟙ˢ := by
  funext α x
  cases x
  case varRight => simp!
  case varLeft x =>
    dsimp! ; unfold id ; simp!
    funext β y
    rw [← Renaming.act_comp]
    congr
    funext δ z
    cases z <;> simp! [Renaming.comp]

def act'_rename {α β γ δ θ : Shape} (u : β →ˢ α ⊕ γ) (f : θ →ʳ β) (e : Expr ((α ⊕ θ) ⊕ δ)):
  act' u (⟦ (α ⇑ʳ f) ʳ⇑ δ ⟧ʳ e) = act' (u ˢ∘ʳ f) e := by
  sorry

def act_rename {β γ δ} (u : γ →ˢ δ) (f : β →ʳ γ) (e : Expr β) :
  ⟦ u ⟧ˢ (⟦ f ⟧ʳ e) = ⟦ u ˢ∘ʳ f ⟧ˢ e := by
  obtain ⟨x, ts⟩ := e
  sorry

def rename_act'_alternative {α γ θ : Shape} (f : α ⊕ γ →ʳ α ⊕ θ) {β δ} (u : β →ˢ α ⊕ γ) (e : Expr ((α ⊕ β) ⊕ δ)):
   ⟦ f ʳ⇑ δ ⟧ʳ act' u e = act' (f ʳ∘ˢ u) e := by
  sorry

def rename_act' {γ θ : Shape} (f : γ →ʳ θ) {α β δ} (u : β →ˢ α ⊕ γ) (e : Expr ((α ⊕ β) ⊕ δ)):
   ⟦ (α ⇑ʳ f) ʳ⇑ δ ⟧ʳ act' u e = act' ((α ⇑ʳ f) ʳ∘ˢ u) e := by
  sorry

def rename_act {γ δ θ} (f : δ →ʳ θ) (u : γ →ˢ δ) (e : Expr γ) :
  ⟦ f ⟧ʳ (⟦ u ⟧ˢ e) = ⟦ f ʳ∘ˢ u ⟧ˢ e := by
  obtain ⟨x, ts⟩ := e
  unfold act

/-- The action of the identity substitution -/
def act_id {γ} (e : Expr γ) : ⟦ 𝟙ˢ ⟧ˢ e = e := by
  induction e
  case apply α δ x ts ih =>
    unfold act
    unfold id
    simp [extend_id δ, ih, Renaming.insertZeroRight, Renaming.act]
    rw [act']
    simp [Renaming.act]
    constructor
    · simp [Renaming.cancelZeroRight, Renaming.extendRight]
    · funext θ y
      sorry

end Substitution
