import HigherRankSyntax.Syntax
import Mathlib.CategoryTheory.Category.Basic

import Init.Notation

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

def extend {γ δ} (f : γ →ʳ δ) (η) : γ ⊕ η →ʳ δ ⊕ η
| _, .varLeft x => .varLeft (f x)
| _, .varRight y => .varRight y

infixl:95 " ⇑ʳ " => Renaming.extend

def extend_id {γ η} : 𝟙ʳ ⇑ʳ η = @id (γ ⊕ η) := by
  funext α x
  rcases x with ⟨x, y⟩ <;> rfl

def extend_comp {γ δ η θ} {g : δ →ʳ η} {f : γ →ʳ δ}:
  (g ∘ʳ f) ⇑ʳ θ = (g ⇑ʳ θ) ∘ʳ (f ⇑ʳ θ) := by
  funext _ x
  cases x <;> rfl

@[reducible]
def act {γ δ} (f : γ →ʳ δ) : Expr γ → Expr δ
  | x ◃ ts => f x ◃ (fun y => act (f ⇑ʳ _) (ts y))

notation:60 "⟦" f "⟧ʳ " e:61 => Renaming.act f e

theorem act_comp {γ} {e : Expr γ} :
  ∀ {δ η} {f : γ →ʳ δ} {g : δ →ʳ η}, ⟦ g ∘ʳ f ⟧ʳ e = ⟦ g ⟧ʳ (⟦ f ⟧ʳ e) := by
  induction e
  case apply ih =>
    intros
    simp [comp, extend_comp]
    funext
    apply ih

theorem comp_assoc {γ δ η θ} {f : γ →ʳ δ} {g : δ →ʳ η} {h : η →ʳ θ} :
  (h ∘ʳ g) ∘ʳ f = h ∘ʳ (g ∘ʳ f) := by rfl

end Renaming
