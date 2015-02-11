module MorphismCompleteness where

open import Data.Product 
open import Relation.Binary.PropositionalEquality
open import Category
open import Container

module _ (C₀ C₁ : Container Type) (α : NaturalTransformation ⟦ C₀ ⟧ ⟦ C₁ ⟧) where
  A : Set
  A = Container.Shapes C₀

  B : A → Set
  B = Container.Positions C₀

  C : Set
  C = Container.Shapes C₁

  D : C → Set
  D = Container.Positions C₁

  α₀ : (X : Set) → (s : A) (t : B s → X) → C
  α₀ X s t = proj₁ (NaturalTransformation.arr α X (s , t))

  α₁ : (X : Set) → (s : A) (t : B s → X) → D (α₀ X s t) → X
  α₁ X s t = proj₂ (NaturalTransformation.arr α X (s , t))

  -- We can produce a container morphism out of α...
  α' : ContainerMorphism C₀ C₁
  α' = mk-cont-morphism (λ s → α₀ (B s) s (λ x → x)) (λ s c → α₁ (B s) s (λ x → x) c)

  -- ...and then we need to show that α' maps to α.
  correct : ContainerNaturalTransformation α' ≡ α
  correct = {!!}
