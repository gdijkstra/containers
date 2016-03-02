{-# OPTIONS --without-K #-}

-- Dependent strength of containers
open import Container.Core

module Container.Strength (F : Container) where

open import lib.Basics

open Container F

□ : {A : Type0} (B : A → Type0) → ⟦ F ⟧₀ A → Type0
□ B (s , t) = (p : Ps s) → B (t p)

φ : {A : Type0} (B : A → Type0) → ⟦ F ⟧₀ (Σ A B) → Σ (⟦ F ⟧₀ A) (□ B)
φ B (s , t) = (⟦ F ⟧₁ fst (s , t)) , (λ p → snd (t p))

φ⁻¹ : {A : Type0} (B : A → Type0) → Σ (⟦ F ⟧₀ A) (□ B) → ⟦ F ⟧₀ (Σ A B)
φ⁻¹ B ((s , t) , p) = s , (λ x → (t x) , (p x))

-- Action of F on dependent functions
bar : {A : Type0} {B : A → Type0}
  → ((x : A) → B x) → (x : ⟦ F ⟧₀ A) → □ B x
bar 𝓼 (s , t) = λ p → 𝓼 (t p)
