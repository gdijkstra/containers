{-# OPTIONS --without-K #-}

open import Category

module Generalised.Core (𝓒 : Cat) where

open Cat 𝓒

open import lib.Base

infix 5 _◁_

record Container : Type1 where
  constructor _◁_
  field
    Sh : Type0
    Ps : Sh → / 𝓒 /

-- Functorial actions
module _ where
  -- Action on objects
  ⟦_⟧₀ : Container → / 𝓒 / → Type0
  ⟦_⟧₀ (Sh ◁ Ps) X = Σ Sh (λ s → 𝓒 [ Ps s , X ])

  -- Action on morphisms
  ⟦_⟧₁ : {X Y : / 𝓒 /} → (F : Container) → 𝓒 [ X , Y ] → ⟦ F ⟧₀ X → ⟦ F ⟧₀ Y
  ⟦_⟧₁ (Sh ◁ Ps) f (s , t) = (s , comp f t)
