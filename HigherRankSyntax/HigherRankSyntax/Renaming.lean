import HigherRankSyntax.Syntax
import Mathlib.CategoryTheory.Category.Basic

def Renaming (γ δ : Shape) := ∀ {{α}}, Var α γ → Var α δ
infix:25 " →ʳ " => Renaming

namespace Renaming

def id {γ} : γ →ʳ γ := fun {{_}} x => x

notation "𝟙ʳ" => Renaming.id

def comp {γ δ η} (f : γ →ʳ δ) (g : δ →ʳ η) : γ →ʳ η :=
  fun {{_}} x => g (f x)

notation:90 g:90 " ∘ʳ " f:90 => Renaming.comp f g

/-- The category of shapes and renamings -/
instance ShapeCat : CategoryTheory.Category Shape where
  Hom := Renaming
  id := @Renaming.id
  comp := comp

@[reducible]
def sum {γ δ θ} (f : γ →ʳ θ) (g : δ →ʳ θ) : γ ⊕ δ →ʳ θ
| _, .varLeft x => f x
| _, .varRight x => g x

infix:30 " ⊕ʳ " => Renaming.sum

@[reducible]
def assocLeft {γ δ θ} : γ ⊕ (δ ⊕ θ) →ʳ (γ ⊕ δ) ⊕ θ :=
  (.varLeft ∘ʳ .varLeft) ⊕ʳ ((.varLeft ∘ʳ .varRight) ⊕ʳ .varRight)

@[reducible]
def assocRight {γ δ θ} : (γ ⊕ δ) ⊕ θ →ʳ γ ⊕ (δ ⊕ θ) :=
  (.varLeft ⊕ʳ (.varRight ∘ʳ .varLeft)) ⊕ʳ (.varRight ∘ʳ .varRight)

@[reducible]
def insertZeroRight {γ} : γ →ʳ γ ⊕ 𝟘 := .varLeft

@[reducible]
def cancelZeroRight {γ} : γ ⊕ 𝟘 →ʳ γ
| _, .varLeft x => x

@[reducible]
def insertZeroLeft {γ} : γ →ʳ 𝟘 ⊕ γ := .varRight

@[reducible]
def cancelZeroLeft {γ} : 𝟘 ⊕ γ →ʳ γ
| _, .varRight x => x

def extendRight {γ δ} (f : γ →ʳ δ) (η) : γ ⊕ η →ʳ δ ⊕ η
| _, .varLeft x => .varLeft (f x)
| _, .varRight y => .varRight y

infixl:95 " ʳ⇑ " => Renaming.extendRight

def extendLeft {γ δ} (η) (f : γ →ʳ δ) : η ⊕ γ →ʳ η ⊕ δ
| _, .varLeft x => .varLeft x
| _, .varRight y => .varRight (f y)

infixl:95 " ⇑ʳ " => Renaming.extendLeft

def extend_id {γ η} : 𝟙ʳ ʳ⇑ η = @id (γ ⊕ η) := by
  funext α x
  rcases x with ⟨x, y⟩ <;> rfl

def extend_comp {γ δ η θ} {g : δ →ʳ η} {f : γ →ʳ δ}:
  (g ∘ʳ f) ʳ⇑ θ = (g ʳ⇑ θ) ∘ʳ (f ʳ⇑ θ) := by
  funext _ x
  cases x <;> rfl

@[reducible]
def act {γ δ} (f : γ →ʳ δ) : Expr γ → Expr δ
  | x ◃ ts => f x ◃ (fun {{_}} y => act (f ʳ⇑ _) (ts y))

notation:60 " ⟦" f "⟧ʳ " e:61 => Renaming.act f e

theorem act_comp {γ} {e : Expr γ} :
  ∀ {δ η} {f : γ →ʳ δ} {g : δ →ʳ η}, ⟦ g ∘ʳ f ⟧ʳ e = ⟦ g ⟧ʳ (⟦ f ⟧ʳ e) := by
  induction e
  case apply α δ x ts ih =>
    intros _ _ f g
    simp [comp, extend_comp]
    funext
    apply ih

theorem comp_assoc {γ δ η θ} {f : γ →ʳ δ} {g : δ →ʳ η} {h : η →ʳ θ} :
  (h ∘ʳ g) ∘ʳ f = h ∘ʳ (g ∘ʳ f) := by rfl

theorem eq_size {γ δ} (f : γ →ʳ δ) (e : Expr γ) : (⟦ f ⟧ʳ e).sizeOf = e.sizeOf := by
  induction e
  case apply γ α x ts ih =>
    sorry

end Renaming
