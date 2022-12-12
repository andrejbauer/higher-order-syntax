open import Agda.Primitive
open import Relation.Unary hiding (_∈_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_,_)

open ≡-Reasoning

import Syntax
import Renaming


module Substitution (Class : Set) where

  open Syntax Class
  open Renaming Class

  -- Lifting of renamings to substitutions, and of variables to expressions

  lift : ∀ {γ δ} → (γ →ʳ δ) → (γ →ˢ δ)

  η : ∀ {γ γˣ clˣ} (x : (γˣ , clˣ) ∈ γ) → Expr (γ ⊕ γˣ) clˣ

  lift 𝟘 = 𝟘
  lift [ x ] = [ η x ]
  lift (ρ₁ ⊕ ρ₂) = lift ρ₁ ⊕ lift ρ₂

  η x = var-left x ` lift (tabulate var-right)

  -- Ideally we would like the following to be the definition of lift,
  -- but Agda termination gets in the way

  lift-map : ∀ {γ δ} (ρ : γ →ʳ δ) → lift ρ ≡ map η ρ
  lift-map 𝟘 = refl
  lift-map [ x ] = refl
  lift-map (ρ₁ ⊕ ρ₂) = cong₂ _⊕_ (lift-map ρ₁) (lift-map ρ₂)

  lift-𝟙ʳ : ∀ {γ} → lift 𝟙ʳ ≡ tabulate (η {γ = γ})
  lift-𝟙ʳ = trans (lift-map 𝟙ʳ) map-tabulate

  -- Identity substitution

  𝟙ˢ : ∀ {γ} → γ →ˢ γ
  𝟙ˢ = lift 𝟙ʳ

  -- Substitution extension

  ⇑ˢ : ∀ {γ δ θ} → γ →ˢ δ → γ ⊕ θ →ˢ δ ⊕ θ
  ⇑ˢ {θ = θ} f =  map [ ⇑ʳ (tabulate var-left) ]ʳ_ f ⊕ lift (tabulate var-right)

  -- The interaction of lifting with various operations

  -- ⇑ˢ-⊕ : ∀ {γ₁ γ₂ δ θ} (f : γ₁ →ˢ δ) (g : γ₂ →ˢ δ) → ⇑ˢ {θ = θ} (f ⊕ g) ≡ f ⊕ ⇑ˢ g

  ⇑ˢ-lift : ∀ {γ δ θ} (ρ : γ →ʳ δ) → ⇑ˢ {θ = θ} (lift ρ) ≡ lift (⇑ʳ ρ)
  ⇑ˢ-lift ρ = cong₂ _⊕_ (trans {!!} (sym (lift-map _))) refl


  -- Action of substitution
  infix 6 [_]ˢ_
  infix 6 _∘ˢ_

  -- -- The naive definition, which Agda does not see as terminating
  -- [_]ˢ_ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr γ cl → Expr δ cl
  -- _∘ˢ_ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → γ →ˢ θ
  -- [ f ]ˢ x ` ts = [ 𝟙ˢ ⊕ (f ∘ˢ ts) ]ˢ (f ∙ x)
  -- g ∘ˢ f = tabulate (λ x → [ ⇑ˢ g ]ˢ f ∙ x)

  -- Instead we use the Bove-Cappreta method, whereby we define the support of [_]ˢ_ and _∘ˢ_, then we define the maps
  -- as partial maps defined on the support, and finally show that the supports are the entire domains.
  -- See doi:10.1017/S0960129505004822

  data defined-[]ˢ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr γ cl → Set

  data defined-∘ˢ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → Set

  actˢ : ∀ {γ δ cl} (f : γ →ˢ δ) (e : Expr γ cl) → defined-[]ˢ f e → Expr δ cl
  compˢ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → defined-∘ˢ g f → (γ →ˢ θ)

  data defined-[]ˢ where
    def-[]ˢ : ∀ {γ γ' δ cl} {f : γ →ˢ δ} {x : (γ' , cl) ∈ γ} {ts : γ' →ˢ γ} (D : defined-∘ˢ f ts) →
                defined-[]ˢ (𝟙ˢ ⊕ (compˢ f ts D)) (f ∙ x) →
                defined-[]ˢ f (x ` ts)

  data defined-∘ˢ where
    def-∘ˢ :  ∀ {γ δ θ} {g : δ →ˢ θ} {f : γ →ˢ δ} →
              (∀ {γ' cl} (x : (γ' , cl) ∈ γ) → defined-[]ˢ (⇑ˢ g) (f ∙ x)) → defined-∘ˢ g f

  actˢ f (x ` ts) (def-[]ˢ D E) = actˢ (𝟙ˢ ⊕ (compˢ f ts D)) (f ∙ x) E

  compˢ g f (def-∘ˢ D) = tabulate (λ x → actˢ (⇑ˢ g) (f ∙ x) (D x))

  -- Showing that actˢ and compˢ are total requires several steps.

  -- The lifting of a renaming is total

  actˢ-lift-total : ∀ {γ δ cl} (ρ : γ →ʳ δ) (e : Expr γ cl) → defined-[]ˢ (lift ρ) e
  actˢ-lift-total ρ (x ` ts) = def-[]ˢ (def-∘ˢ (λ y → {!!})) {!!}

  -- The identity substittion is total
  actˢ-𝟙ˢ-total : ∀ {γ cl} (e : Expr γ cl) → defined-[]ˢ 𝟙ˢ e
  actˢ-𝟙ˢ-total (x ` ts) = def-[]ˢ {!!} {!!}


  total-actˢ : ∀ {γ δ cl} (f : γ →ˢ δ) (e : Expr γ cl) → defined-[]ˢ f e
  total-compˢ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → defined-∘ˢ g f

  total-actˢ f (x ` ts) = def-[]ˢ (total-compˢ f ts) {!!}

  total-compˢ {γ = γ} f g = def-∘ˢ λ {γ' cl} (x : (γ' , cl) ∈ γ) → {!!}


  -- Finally, the definitions we wanted to get

  [_]ˢ_ : ∀ {γ δ cl} (f : γ →ˢ δ) → Expr γ cl → Expr δ cl
  [ f ]ˢ e = actˢ f e (total-actˢ f e)

  _∘ˢ_ : ∀ {γ δ θ} (g : δ →ˢ θ) (f : γ →ˢ δ) → γ →ˢ θ
  g ∘ˢ f = compˢ g f (total-compˢ g f)
