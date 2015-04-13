module Monad where

open import Relation.Binary.PropositionalEquality
open import Container
open import Category
open import Data.Unit
open import Data.Product
open import Function renaming ( _∘_ to _∘'_ )

record ContainerMonad (M : Container Type) : Set where
  constructor mk-cont-monad

  open Container.Container M renaming ( Shapes to S ; Positions to P )
  
  field
    s : S -- Every s : S gives rise to a natural transformation 1 -> M.
    θ : (s : S) → (t : P s → S) → S 
    ρ₀ : (s : S) → (t : P s → S) → P (θ s t) → P s
    ρ₁ : (s : S) → (t : P s → S) → (p : P (θ s t)) → P (t (ρ₀ s t p))

module _ {M : Container Type} (mon : ContainerMonad M) where
  open ContainerMonad mon

  open Container.Container M renaming ( Shapes to S ; Positions to P )

  ρ : (s : S) → (t : P s → S) → P (θ s t) → Σ (P s) (λ r → P (t r))
  ρ s t p = ρ₀ s t p , ρ₁ s t p

  η-morphism : ContainerMorphism Id M
  η-morphism = mk-cont-morphism (λ _ → s) (λ _ _ → tt)

  μ-morphism : ContainerMorphism (M ∘ M) M
  μ-morphism = mk-cont-morphism (uncurry θ) (uncurry ρ)

  η : (X : Set) → X → ⟦ M ⟧₀ X
  η X x = s , (λ _ → x)

  μ : (X : Set) → ⟦ M ⟧₀ (⟦ M ⟧₀ X) → ⟦ M ⟧₀ X
  μ X (s , t) = θ s (proj₁ ∘' t) , (λ x → proj₂ (t (ρ₀ s (proj₁ ∘' t) x)) (ρ₁ s (proj₁ ∘' t) x))

  -- Here we are trying to specialise the monad laws to container
  -- monads.
  module _ (X : Set) where
    μ-assoc : Set
    μ-assoc = (x : ⟦ M ⟧₀ (⟦ M ⟧₀ (⟦ M ⟧₀ X))) → μ _ (⟦ M ⟧₁ (μ X) x) ≡ μ _ (μ (⟦ M ⟧₀ X) x)

    η-left-unit : Set
    η-left-unit = (x : ⟦ M ⟧₀ X) → x ≡ μ _ (⟦ M ⟧₁ (η X) x)
  
    -- For any s, t : (s : S) × (P s → X)
    --  - θ s' (const s) ≡ s'
    --  - θ s (const s') ≡ s'
    --  - t ≡ t ∘ (ρ₀ s' (const s)) -- left
    --  - t ≡ t ∘ (ρ₁ s (const s')) -- right
    -- Types of these?

    η-right-unit : Set
    η-right-unit = (x : ⟦ M ⟧₀ X) → x ≡ μ _ (η (⟦ M ⟧₀ X) x)

    -- -- This will be very messy.
    -- module _ (θ-law : (s' : S) → θ s' (const s) ≡ s) where -- (ρ₀-law : (s' : S) (t : P s' → X) → t ≡ t ∘ (ρ₀ s' (const s))) where --(ρ₀-law : t ≡ t ∘ (ρ₀ s (const s))) where
    --   η-left-unit-pf : η-left-unit
    --   η-left-unit-pf (s' , t) = {!!}

