module Monad where

open import Container
open import Category
open import Data.Unit
open import Data.Product

record ContainerMonad (M : Container Type) : Set where
  constructor mk-cont-monad

  open Container.Container M renaming ( Shapes to S ; Positions to P )
  
  field
    s : S -- Every s : S gives rise to a natural transformation 1 -> M.
    θ : Σ S (λ q → P q → S) → S -- M-algebra structure on S.
    ρ : (st : Σ S (λ q → P q → S)) → P (θ st) → Σ (P (proj₁ st)) (λ r → P (proj₂ st r))

module _ {M : Container Type} (mon : ContainerMonad M) where
  open ContainerMonad mon

  η-morphism : ContainerMorphism Id M
  η-morphism = mk-cont-morphism (λ _ → s) (λ _ _ → tt)

  μ-morphism : ContainerMorphism (M ∘ M) M
  μ-morphism = mk-cont-morphism θ ρ

  η : (X : Set) → X → ⟦ M ⟧₀ X
  η X x = s , (λ _ → x)

  μ' : (X : Set) → ⟦ M ∘ M ⟧₀ X → ⟦ M ⟧₀ X
  μ' X (s , t) = θ s , (λ z → t (ρ s z))

  -- TODO: Do this generally in Container.agda
  to : (X : Set) → ⟦ M ⟧₀ (⟦ M ⟧₀ X) → ⟦ M ∘ M ⟧₀ X
  to X (α , β) = (α , (λ x → proj₁ (β x))) , (λ { (p , p') → proj₂ (β p) p' })
  
  μ : (X : Set) → ⟦ M ⟧₀ (⟦ M ⟧₀ X) → ⟦ M ⟧₀ X
  μ X (s , t) with to X (s , t)
  ... | α , β = θ α , (λ x → β (ρ α x))

record MonadAlgebra {M : Container Type} (mon : ContainerMonad M) (X : Set) (h : ⟦ M ⟧₀ X → X) : Set₁ where
  constructor mk-monad-alg

  open Container.Container M renaming ( Shapes to S ; Positions to P )
  open ContainerMonad mon


