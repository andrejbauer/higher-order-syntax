{-# OPTIONS --sized-types #-}

open import Data.Nat
open import Size

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

{-

   A formalization of (raw) syntax with higher-order binders.

   We define a notion of syntax which allows for higher-order binders, variables and substitutions. Ordinary notions of
   variables are special cases:

   * order 1: ordinary variables and substitutions, for example those of λ-calculus
   * order 2: meta-variables and their instantiations
   * order 3: symbols (term formers) in dependent type theory, such as Π, Σ, W

   The syntax is parameterized by a type Class of syntactic classes. For example, in dependent type theory there might
   be two syntactic classes, ty and tm, corresponding to type and term expressions.

-}


module Syntax (Class : Set) where

  infixl 6 _⊕_

  {- Shapes are a kind of variable contexts. They assign to each variable its syntactic arity, which is a syntactic
     class and a binding shape. We model shapes as binary trees so that it is easy to concatenate two of them. A more
     traditional approach models shapes as lists, in which case one has to append lists. -}

  data Shape : ∀ { i : Size } → Set where
    𝟘 : ∀ {i} → Shape {i} -- the empty shape
    [_,_] : ∀ {i} (Γ : Shape {i}) (cl : Class) → Shape {↑ i} -- the shape with precisely one variable
    _⊕_ : ∀ {j k} → Shape {j} → Shape {k} → Shape {j ⊔ˢ k} -- disjoint sum of shapes

  infix 5 [_,_]∈_

  {- The de Bruijn indices are binary numbers because shapes are binary trees.
     [ A , Δ ]∈ Γ is the set of variable indices in Γ whose arity is (A , Δ). -}
  data [_,_]∈_ : ∀ {i} {j : Size< i} → Shape {j} → Class → Shape {i} → Set where
    var-here : ∀ {i} {Ξ : Shape {i}} {A} → [ Ξ , A ]∈  [ Ξ , A ]
    var-left :  ∀ {j k} {i : Size< j} {Ξ : Shape {i}} {A} {Γ : Shape {j}} {Δ : Shape {k}} → [ Ξ , A ]∈ Γ → [ Ξ , A ]∈ Γ ⊕ Δ
    var-right : ∀ {j k} {i : Size< k} {Ξ : Shape {i}} {A} {Γ : Shape {j}} {Δ : Shape {k}} → [ Ξ , A ]∈ Δ → [ Ξ , A ]∈ Γ ⊕ Δ

  {- Examples:

  postulate ty : Class -- type class
  postulate tm : Class -- term class

  ordinary-variable-arity : Class → Shape
  ordinary-variable-arity c = [ 𝟘 , c ]

  binary-type-metavariable-arity : Shape
  binary-type-metavariable-arity = [ [ 𝟘 , tm ] ⊕ [ 𝟘 , tm ] , ty ]

  Π-arity : Shape
  Π-arity = [ [ 𝟘 , ty ] ⊕ [ [ 𝟘 , tm ] , tm ] , ty ]

  -}

  {- The order of a shape -}

  -- order : Shape → ℕ
  -- order 𝟘 = zero
  -- order [ Γ , cl ] = suc (order Γ)
  -- order (Γ ⊕ Δ) = order Γ ⊔ order Δ


  {- Because everything is a variable, even symbols, there is a single expression constructor
     x ` ts which forms and expression by applying the variable x to arguments ts. -}

  infix 9 _`_

  data Expr : Shape → Class → Set where
    _`_ : ∀ {Γ A Ξ} (x : [ Ξ , A ]∈ Γ) → (ts : ∀ {Δ B} (y : [ Δ , B ]∈ Ξ) → Expr (Γ ⊕ Δ) B) → Expr Γ A

  -- Syntactic equality of expressions

  infix 4 _≈_

  data _≈_ : ∀ {Γ A} → Expr Γ A → Expr Γ A → Set where
    ≈-≡ : ∀ {Γ A} {t u : Expr Γ A} (ξ : t ≡ u) → t ≈ u
    ≈-` : ∀ {Γ A Ξ} {x : [ Ξ , A ]∈ Γ} →
            {ts us : ∀ {Δ B} (y : [ Δ , B ]∈ Ξ) → Expr (Γ ⊕ Δ) B}
            (ξ : ∀ {Δ B} (y : [ Δ , B ]∈ Ξ) → ts y ≈ us y) → x ` ts ≈ x ` us

  ≈-refl : ∀ {Γ A} {t : Expr Γ A} → t ≈ t
  ≈-refl = ≈-≡ refl

  ≈-sym : ∀ {Γ A} {t u : Expr Γ A} → t ≈ u → u ≈ t
  ≈-sym (≈-≡ ξ) = ≈-≡ (sym ξ)
  ≈-sym (≈-` ξ) = ≈-` λ y → ≈-sym (ξ y)

  ≈-trans : ∀ {Γ A} {t u v : Expr Γ A} → t ≈ u → u ≈ v → t ≈ v
  ≈-trans (≈-≡ refl) ξ = ξ
  ≈-trans (≈-` ζ) (≈-≡ refl) = ≈-` ζ
  ≈-trans (≈-` ζ) (≈-` ξ) = ≈-` (λ y → ≈-trans (ζ y) (ξ y))
