import HigherRankedSyntax.Syntax

import Init.Notation

def Renaming (γ δ : Shape) := ∀ {{α}}, Var α γ → Var α δ
infix:25 " →ʳ " => Renaming

namespace Renaming

@[reducible, simp]
def id {γ} : γ →ʳ γ := fun {{_}} x => x

notation "𝟙ʳ" => Renaming.id

@[simp]
def comp {γ δ η} (g : δ →ʳ η) (f : γ →ʳ δ) : γ →ʳ η :=
  fun {{_}} x => g (f x)

infixr:90 " ∘ʳ " => Renaming.comp

@[reducible]
def extend {γ δ} (f : γ →ʳ δ) (η) : γ ⊕ η →ʳ δ ⊕ η
| _, .varLeft x => .varLeft (f x)
| _, .varRight y => .varRight y

infixl:95 " ⇑ʳ " => Renaming.extend

def extend_id {γ η} : 𝟙ʳ ⇑ʳ η = @id (γ ⊕ η) := by
  funext α x
  rcases x with ⟨x, y⟩ <;> rfl

def extend_comp {γ δ η θ} {g : δ →ʳ η} {f : γ →ʳ δ}:
  (g ∘ʳ f) ⇑ʳ θ = (g ⇑ʳ θ) ∘ʳ (f ⇑ʳ θ) := by
  funext α x
  cases x <;> rfl

def act {γ δ} (f : γ →ʳ δ) : Expr γ → Expr δ
  | x ◃ ts => f x ◃ (fun y => act (f ⇑ʳ _) (ts y))

end Renaming
