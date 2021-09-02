open import Induction.WellFounded
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

import Syntax
import Renaming

module Substitution (Class : Set) where

  open Syntax Class
  open Renaming Class

  -- the set of substitutions

  infix 5 _→ˢ_

  _→ˢ_ : Shape → Shape → Set
  Γ →ˢ Δ = ∀ {Θ} {A} (x : [ Θ , A ]∈ Γ) → Arg Δ Θ A

  -- equality of substitutions

  infix 4 _≈ˢ_

  _≈ˢ_ : ∀ {Γ} {Δ} (f g : Γ →ˢ Δ) → Set
  f ≈ˢ g = ∀ {Θ} {A} (x : [ Θ , A ]∈ _) → f x ≈ g x

  -- equality of substitutions is an equivalence relation

  ≈ˢ-refl : ∀ {Γ} {Δ} {f : Γ →ˢ Δ} → f ≈ˢ f
  ≈ˢ-refl x = ≈-refl

  ≈ˢ-sym : ∀ {Γ} {Δ} {f g : Γ →ˢ Δ} → f ≈ˢ g → g ≈ˢ f
  ≈ˢ-sym ξ x = ≈-sym (ξ x)

  ≈ˢ-trans : ∀ {Γ} {Δ} {f g h : Γ →ˢ Δ} → f ≈ˢ g → g ≈ˢ h → f ≈ˢ h
  ≈ˢ-trans ζ ξ x = ≈-trans (ζ x) (ξ x)

  -- identity substitution

  -- -- Definition of identity substitution which does not require any magic
  -- 𝟙ˢ : ∀ {Γ} → Γ →ˢ Γ
  -- 𝟙ˢ {𝟘} ()
  -- 𝟙ˢ {[ Γ , A ]} var-here = var-left var-here ` λ y →  [ ⇑ʳ var-right ]ʳ 𝟙ˢ y
  -- 𝟙ˢ {Γ Syntax.⊕ Δ} (var-left x) =  [ ⇑ʳ var-left ]ʳ 𝟙ˢ x
  -- 𝟙ˢ {Γ Syntax.⊕ Δ} (var-right y) = [ ⇑ʳ var-right ]ʳ 𝟙ˢ y

  -- -- Definition of identity substitution using magic
  -- {-# TERMINATING #-}
  -- 𝟙ˢ : ∀ {Γ} → Γ →ˢ Γ
  -- 𝟙ˢ x =  var-left x ` λ y →  [ 2-to-3-right ]ʳ 𝟙ˢ y

  -- definition of identity substitution using well-founded recursion
  𝟙ˢ : ∀ {Γ} → Γ →ˢ Γ
  𝟙ˢ = rec-∈
         (λ {Γ} {Θ} {A} _ → Arg Γ Θ A)
         (λ x r → var-left x ` λ y → [ ⇑ʳ var-right ]ʳ r y)

  -- Equational characterization of identity substitution

  unfold-𝟙ˢ : ∀ {Γ Θ A} (x : [ Θ , A ]∈ Γ) →
              𝟙ˢ x ≈ var-left x ` (λ y → [ ⇑ʳ var-right ]ʳ 𝟙ˢ y)
  unfold-𝟙ˢ {Γ} {Θ} {A} x =
    unfold-rec-∈
      (λ {Γ} {Θ} {A} _ → Arg Γ Θ A)
      (λ x r → var-left x ` λ y → [ ⇑ʳ var-right ]ʳ r y)
      (λ t u → t ≈ u)
      (λ _ ξ → ≈-` (λ y → []ʳ-resp-≈ (⇑ʳ var-right) (ξ y)))

  -- substitution sum

  [_,_]ˢ : ∀ {Γ Δ Θ} (f : Γ →ˢ Θ) (g : Δ →ˢ Θ) → Γ ⊕ Δ →ˢ Θ
  [ f , g ]ˢ (var-left x) = f x
  [ f , g ]ˢ (var-right y) = g y

  -- substiutions sum respects equality

  [,]ˢ-resp-≈ˢ : ∀ {Γ Δ Θ} {f₁ f₂ : Γ →ˢ Θ} {g₁ g₂ : Δ →ˢ Θ} → f₁ ≈ˢ f₂ → g₁ ≈ˢ g₂ → [ f₁ , g₁ ]ˢ ≈ˢ [ f₂ , g₂ ]ˢ
  [,]ˢ-resp-≈ˢ ζ ξ (var-left x) = ζ x
  [,]ˢ-resp-≈ˢ ζ ξ (var-right y) = ξ y

  -- substitution extension

  ⇑ˢ : ∀ {Γ Δ Θ} → Γ →ˢ Δ → Γ ⊕ Θ →ˢ Δ ⊕ Θ
  ⇑ˢ f (var-left x) =  [ ⇑ʳ var-left ]ʳ f x
  ⇑ˢ f (var-right y) =  [ ⇑ʳ var-right ]ʳ 𝟙ˢ y

  -- substitution respects equality

  ⇑ˢ-resp-≈ˢ : ∀ {Γ Δ Θ} {f g : Γ →ˢ Δ} → f ≈ˢ g → ⇑ˢ {Θ = Θ} f ≈ˢ ⇑ˢ g
  ⇑ˢ-resp-≈ˢ ξ (var-left x) = []ʳ-resp-≈ _ (ξ x)
  ⇑ˢ-resp-≈ˢ ξ (var-right y) = ≈-refl

  infixl 7 _ʳ∘ˢ_

  _ʳ∘ˢ_ : ∀ {Γ Δ Θ} (ρ : Δ →ʳ Θ) (f : Γ →ˢ Δ) → Γ →ˢ Θ
  (ρ ʳ∘ˢ f) x = [ ⇑ʳ ρ ]ʳ f x

  -- the action of a substitution on an expression
  module _ where

    open All wf-≺

    assoc-right : ∀ {Δ Θ Ξ} → (Δ ⊕ Θ) ⊕ Ξ →ʳ Δ ⊕ (Θ ⊕ Ξ)
    assoc-right (var-left (var-left x)) = var-left x
    assoc-right (var-left (var-right y)) = var-right (var-left y)
    assoc-right (var-right z) = var-right (var-right z)

    assoc-left : ∀ {Δ Θ Ξ} → Δ ⊕ (Θ ⊕ Ξ) →ʳ (Δ ⊕ Θ) ⊕ Ξ
    assoc-left (var-left x) = var-left (var-left x)
    assoc-left (var-right (var-left y)) = var-left (var-right y)
    assoc-left (var-right (var-right z)) = var-right z

    infix 6 [_]ˢ_
    [_]ˢ_ : ∀ {Γ Δ A} (f : Γ →ˢ Δ) → Expr Γ A → Expr Δ A

    [_]ˢ_ f (x ` ts) = sb x (λ y → [ ⇑ˢ f ]ˢ ts y) (f x)
      where
       sb-right : ∀ {Γ Θ A} (x : [ Θ , A ]∈ Γ) → ∀ {Δ} → (Γ →ˢ Δ) → Arg Γ Θ A → Arg Δ Θ A
       sb-right =
         wfRec _
           (λ Θ → ∀ {Γ A} (x : [ Θ , A ]∈ Γ) → ∀ {Δ} → (Γ →ˢ Δ) → Arg Γ Θ A → Arg Δ Θ A)
           (λ Θ r x f →
              λ { (var-left y ` ts) → {!!}
                ; (var-right y ` ts) → var-right y ` λ z → r _ (≺-∈ {!!}) {!!} {!!} (ts z)})
           _


       sb : ∀ {Γ Θ A} (x : [ Θ , A ]∈ Γ) → ∀ {Δ} → (Θ →ˢ Δ) → Expr (Δ ⊕ Θ) A → Expr Δ A
       sb =
         rec-∈
           (λ {Γ} {Θ} {A} _ → ∀ {Δ} → (Θ →ˢ Δ) → Expr (Δ ⊕ Θ) A → Expr Δ A)
           (λ x r g →
              λ { (var-left x ` ts) → x ` λ y → {! ts y!}
                ; (var-right x ` ts) → r x (λ y → {!ts y!}) (g x)})

       -- sb g (var-left x ` ts) = x ` λ y → sbb [ 𝟙ˢ , g ]ˢ (ts y)
       -- sb g (var-right x ` ts) =  {!  g x!}





    -- [_]ˢ_ {Γ} =
    --   wfRec
    --     _
    --     (λ Γ → ∀ {Δ B} (f : Γ →ˢ Δ) → Expr Γ B → Expr Δ B)
    --     (λ {Γ r {Δ} {B} f (x ` ts) →
    --        r (Δ ⊕ _) {!!} {!!} (f x)}
    --     )
    --     Γ

  -- {-# TERMINATING #-}
  -- [_]ˢ_ : ∀ {Γ Δ B} (f : Γ →ˢ Δ) → Expr Γ B → Expr Δ B
  -- [ f ]ˢ x ` ts =  [ [ 𝟙ˢ , (λ z → [ ⇑ˢ f ]ˢ ts z) ]ˢ ]ˢ f x

  -- composition of a renaming and a substitutition

  infixl 7 _ˢ∘ʳ_

  _ˢ∘ʳ_ :  ∀ {Γ Δ Θ} (f : Δ →ˢ Θ) (ρ : Γ →ʳ Δ) → Γ →ˢ Θ
  (f ˢ∘ʳ ρ) x = f (ρ x)

  assoc-rightʳ : ∀ {Γ Δ Θ} → (Γ ⊕ Δ) ⊕ Θ →ʳ Γ ⊕ (Δ ⊕ Θ)
  assoc-rightʳ (var-left (var-left x)) = var-left x
  assoc-rightʳ (var-left (var-right y)) = var-right (var-left y)
  assoc-rightʳ (var-right z) = var-right (var-right z)

  assoc-leftʳ : ∀ {Γ Δ Θ} → Γ ⊕ (Δ ⊕ Θ) →ʳ (Γ ⊕ Δ) ⊕ Θ
  assoc-leftʳ (var-left x) = var-left (var-left x)
  assoc-leftʳ (var-right (var-left y)) = var-left (var-right y)
  assoc-leftʳ (var-right (var-right z)) = var-right z

  subst-args : ∀ {Γ Δ Θ A} (f : Δ →ˢ Θ) → Arg Γ Δ A → Arg Γ Θ A
  subst-args f (var-left x ` ts) = var-left x ` λ y → {!!}
  subst-args f (var-right x ` ts) = {!!}

  -- [_]ˢ_ : ∀ {Γ Δ B} (f : Γ →ˢ Δ) → Expr Γ B → Expr Δ B
  -- [_]ˢ_ {Γ = 𝟘} f (() ` _)
  -- [_]ˢ_ {Γ = [ Γ , A ]} f (var-here ` ts) =  [ {!!} ]ˢ f var-here
  -- [_]ˢ_ {Γ = Γ ⊕ Δ} f (var-left x ` ts) = {! f (var-left x)!}
  -- [_]ˢ_ {Γ = Γ ⊕ Δ} f (var-right y ` ts) = {!!}

  -- -- substitution respects equality

  -- []ˢ-resp-≈ : ∀ {Γ Δ A} (f : Γ →ˢ Δ) {t u : Expr Γ A} → t ≈ u → [ f ]ˢ t ≈ [ f ]ˢ u

  -- []ˢ-resp-≈ˢ : ∀ {Γ Δ A} {f g : Γ →ˢ Δ} (t : Expr Γ A) → f ≈ˢ g → [ f ]ˢ t ≈ [ g ]ˢ t

  -- []ˢ-resp-≈-≈ˢ : ∀ {Γ Δ A} {f g : Γ →ˢ Δ} {t u : Expr Γ A} → f ≈ˢ g → t ≈ u → [ f ]ˢ t ≈ [ g ]ˢ u

  -- []ˢ-resp-≈ f (≈-≡ ξ) = ≈-≡ (cong ( [ f ]ˢ_) ξ)
  -- []ˢ-resp-≈ f (≈-` ξ) = ?

  -- []ˢ-resp-≈ˢ (x ` ts) ξ = []ˢ-resp-≈-≈ˢ
  --                            ([,]ˢ-resp-≈ˢ (λ x → ≈-refl) λ y → []ˢ-resp-≈ˢ (ts y) ((⇑ˢ-resp-≈ˢ ξ)))
  --                            (ξ x)

  -- []ˢ-resp-≈-≈ˢ {g = g} {t = t} ζ ξ = ≈-trans ([]ˢ-resp-≈ˢ t ζ) ([]ˢ-resp-≈ g ξ)

  -- -- composition of substitutitions

  -- infixl 7 _∘ˢ_

  -- _∘ˢ_ : ∀ {Γ Δ Θ} (g : Δ →ˢ Θ) (f : Γ →ˢ Δ) → Γ →ˢ Θ
  -- (g ∘ˢ f) x =  [ ⇑ˢ g ]ˢ f x

  -- -- composition of a renaming and a substitutition

  -- infixl 7 _ˢ∘ʳ_

  -- _ˢ∘ʳ_ :  ∀ {Γ Δ Θ} (f : Δ →ˢ Θ) (ρ : Γ →ʳ Δ) → Γ →ˢ Θ
  -- (f ˢ∘ʳ ρ) x = f (ρ x)

  -- -- extension respects identity

  -- ⇑ˢ-resp-𝟙ˢ : ∀ {Γ Θ} → ⇑ˢ {Θ = Θ} (𝟙ˢ {Γ = Γ}) ≈ˢ 𝟙ˢ
  -- ⇑ˢ-resp-𝟙ˢ {Γ = Γ} (var-left x) = ≈-refl
  -- ⇑ˢ-resp-𝟙ˢ {Γ = Γ} (var-right y) = ≈-refl

  -- -- extension of a substitutition and a renaming respects composition

  -- ⇑ˢ-resp-ˢ∘ʳ : ∀ {Γ Δ Ξ Θ} {f : Δ →ˢ Ξ} {ρ : Γ →ʳ Δ} →
  --               ⇑ˢ {Θ = Θ} (f ˢ∘ʳ ρ) ≈ˢ ⇑ˢ f ˢ∘ʳ ⇑ʳ ρ
  -- ⇑ˢ-resp-ˢ∘ʳ {f = f} (var-left x) = ≈-refl
  -- ⇑ˢ-resp-ˢ∘ʳ {f = f} (var-right y) = ≈-refl

  -- ⇑ˢ-resp-ʳ∘ˢ : ∀ {Γ Δ Ξ Θ} {ρ : Δ →ʳ Ξ} {f : Γ →ˢ Δ} →
  --               ⇑ˢ {Θ = Θ} (ρ ʳ∘ˢ f) ≈ˢ ⇑ʳ ρ ʳ∘ˢ ⇑ˢ f

  -- ⇑ˢ-resp-ʳ∘ˢ {f = f} (var-left x) =
  --   ≈-trans
  --     (≈-sym ([∘ʳ] (f x)))
  --     (≈-trans
  --       ([]ʳ-resp-≡ʳ (f x) (λ { (var-left y) → refl ; (var-right z) → refl}))
  --       ([∘ʳ] (f x)))
  -- ⇑ˢ-resp-ʳ∘ˢ {ρ = ρ} {f = f} (var-right y) =
  --   ≈-trans
  --     ([]ʳ-resp-≡ʳ (𝟙ˢ y) (λ { (var-left _) → refl ; (var-right _) → refl}))
  --     ([∘ʳ] (𝟙ˢ y))

  -- -- composition of a renaming and a substitution respects equality

  -- [ˢ∘ʳ] : ∀ {Γ Δ Θ A} {f : Δ →ˢ Θ} {ρ : Γ →ʳ Δ} → (t : Expr Γ A) →
  --         [ f ˢ∘ʳ ρ ]ˢ t ≈ [ f ]ˢ [ ρ ]ʳ t
  -- [ˢ∘ʳ] {f = f} {ρ = ρ} (x ` ts) =
  --   []ˢ-resp-≈ˢ
  --     (f (ρ x))
  --     (λ { (var-left _) → ≈-refl
  --        ; (var-right y) → ≈-trans
  --                            ([]ˢ-resp-≈ˢ (ts y) (λ { (var-left _) → ≈-refl ; (var-right _) → ≈-refl}))
  --                            ([ˢ∘ʳ] (ts y))})

  -- {-# TERMINATING #-}
  -- [ʳ∘ˢ] : ∀ {Γ Δ Θ A} {ρ : Δ →ʳ Θ} {f : Γ →ˢ Δ} (t : Expr Γ A) →
  --         [ ρ ʳ∘ˢ f ]ˢ t ≈ [ ρ ]ʳ [ f ]ˢ t
  -- [ʳ∘ˢ] {ρ = ρ} {f = f} (x ` ts) =
  --   ≈-trans
  --     (≈-trans
  --        (≈-sym ([ˢ∘ʳ] (f x)))
  --        ([]ˢ-resp-≈ˢ (f x)
  --           (λ { (var-left y) →
  --                  ≈-trans
  --                    (𝟙ˢ-≈ (ρ y))
  --                    (≈-trans
  --                      (≈-` λ y → ≈-trans
  --                                   ([]ʳ-resp-≡ʳ (𝟙ˢ y) (λ { (var-left _) → refl ; (var-right _) → refl}))
  --                                   ([∘ʳ] (𝟙ˢ y)))
  --                      ([]ʳ-resp-≈ (⇑ʳ ρ) (≈-sym (𝟙ˢ-≈ y))))
  --           ; (var-right y) → ≈-trans ([]ˢ-resp-≈ˢ (ts y) ⇑ˢ-resp-ʳ∘ˢ) ([ʳ∘ˢ] (ts y))})))
  --     ([ʳ∘ˢ] (f x))

  -- -- composition of substitution respects identity
  -- [𝟙ˢ] : ∀ {Γ A} (t : Expr Γ A) → [ 𝟙ˢ ]ˢ t ≈ t
  -- [𝟙ˢ] {Γ = 𝟘} (() ` _)
  -- [𝟙ˢ] {Γ = [ Γ , A ]} (var-here ` ts) = {!!}
  -- [𝟙ˢ] {Γ = Γ ⊕ Δ} t = {!!}


  -- -- composition of substitutions respects equality

  -- {-# TERMINATING #-}
  -- [∘ˢ] : ∀ {Γ Δ Θ A} {g : Δ →ˢ Θ} {f : Γ →ˢ Δ} (t : Expr Γ A) → [ g ∘ˢ f ]ˢ t ≈ [ g ]ˢ [ f ]ˢ t
  -- [∘ˢ] {g = g} {f = f} (x ` ts) =
  --   ≈-trans
  --     (≈-sym ([∘ˢ] (f x)))
  --     (≈-trans
  --        ([]ˢ-resp-≈ˢ (f x)
  --           (λ { (var-left y) → {!!}
  --              ; (var-right _) → {!!}}))
  --        ([∘ˢ] (f x)))
