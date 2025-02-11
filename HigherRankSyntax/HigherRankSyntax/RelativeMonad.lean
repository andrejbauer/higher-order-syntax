import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic

import HigherRankSyntax.Syntax
import HigherRankSyntax.Renaming

def ArityCat := ShapeCat

open CategoryTheory

structure VarRen (γ δ : Shape) : Type where
  arity : Arity
  var : Var arity γ
  ren : arity →ʳ δ

#check Functor.category

/-- The object part of the variables functor -/
def 𝕁' (γ : Shape) : Arity ⥤ Type where
  obj := VarRen γ
  map := fun ρ xσ => { arity := xσ.arity, var := xσ.var, ren := ρ ∘ʳ xσ.ren }

/-- The variables functor -/
def 𝕁 : Shape ⥤ (Arity ⥤ Type) where
  obj := 𝕁'
  map := fun {γ γ'} ρ =>
    { app := fun δ xσ => { arity := xσ.arity, var := ρ xσ.var, ren := xσ.ren } }

/-- The object part of the expression functor -/
def 𝕋' (γ : Shape) : Arity ⥤ Type where

  obj := Expr γ

  map := fun {δ δ' f} => f.actBound

  map_id := by
    intro δ
    funext e
    apply Renaming.actBound.map_id

  map_comp := by
    intro δ₁ δ₂ δ₃ f g
    funext e
    simp
    apply Renaming.actBound.map_comp

/-- The expressions functor -/
def 𝕋 : Shape ⥤ (Arity ⥤ Type) where

  obj := 𝕋'

  map := fun {γ γ'} f =>
    { app := fun _ => Renaming.actFree f
      naturality := by
        intros δ δ' g
        funext e
        simp [𝕋']
        apply Renaming.actFree_actBound
    }

  map_id := by
    intro γ
    simp [𝕋']
    congr
    funext δ e
    apply Renaming.actFree.map_id

  map_comp := by
    intro γ₁ γ₂ γ₃ f g
    simp [𝕋']
    congr
    funext δ e
    apply Renaming.actFree.map_comp
