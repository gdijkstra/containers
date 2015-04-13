{-# OPTIONS --without-K #-}

open import Category hiding (_∘_)
open import Container

module FreeMonadAlgebras (F : Container Type) where

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import FreeMonad F
open ≡-Reasoning

-- Aliases to make things a bit more readable.
private 
  F₀ : Set → Set
  F₀ = ⟦ F ⟧₀
  
  F₁ : {X Y : Set} → (X → Y) → (F₀ X → F₀ Y)
  F₁ = ⟦ F ⟧₁

-- TODO: Use the definitions from Algebras.agda
record F-Alg₀ : Set₁ where
  constructor mk-F-alg
  field
    X : Set
    θ : F₀ X → X

record F-Alg₁ (a b : F-Alg₀) : Set₁ where
  constructor mk-F-alg-morphism
  open F-Alg₀ a
  open F-Alg₀ b renaming ( X to Y ; θ to ρ )
  field
    f : X → Y
    comm : (x : F₀ X) → f (θ x) ≡ ρ (F₁ f x)

record F*-MonAlg₀ : Set₁ where
  constructor mk-F*-MonAlg
  field
    X : Set
    θ : F*₀ X → X
    comm-μ : (x : F*₀ (F*₀ X)) → θ (F*₁ θ x) ≡ θ (μ x)
    comm-η : (x : X) → x ≡ θ (η x)

record F*-Alg₁ (a b : F*-MonAlg₀) : Set₁ where
  constructor mk-F-alg-morphism
  open F*-MonAlg₀ a
  open F*-MonAlg₀ b renaming ( X to Y ; θ to ρ )
  field
    f : X → Y
    comm : (x : F*₀ X) → f (θ x) ≡ ρ (F*₁ f x)
-- If we want to be precise, we also have to consider comm-μ and
-- comm-η.

open import FunExt

module _ (X : Set) (θ : F₀ X → X) where
  to : F*₀ X → X
  to = F*₀-elim X X id θ

  to-comm-η : (x : X) → x ≡ to (η x)
  to-comm-η x = refl

  to-comm-μ : (x : F*₀ (F*₀ X)) → to (F*₁ to x) ≡ to (μ x)
  to-comm-μ =
    F*₀-ind (F*₀ X)
            (λ x → to (F*₁ to x) ≡ to (μ x)) -- goal
            (λ x → refl) -- η case holds by definition
            (λ s t ind-hyp →
              begin
                to (F*₁ to (c (s , t)))
                  ≡⟨ refl ⟩ -- def. of F*
                to (c (s , F*₁ to ∘ t))
                  ≡⟨ refl ⟩ -- def. of to
                θ (s , to ∘ F*₁ to ∘ t)
                  -- apply induction hypothesis
                  ≡⟨ cong (λ x → θ (s , x)) (fun-ext (to ∘ F*₁ to ∘ t) (to ∘ μ ∘ t) ind-hyp) ⟩
                θ (s , to ∘ μ ∘ t)
                  ≡⟨ refl ⟩ -- def. of to
                to (c (s , μ ∘ t))
                  ≡⟨ refl ⟩ -- def. of μ 
                to (μ (c (s , t))) ∎)

to₀ : F-Alg₀ → F*-MonAlg₀
to₀ (mk-F-alg X θ) = mk-F*-MonAlg X (to X θ) (to-comm-μ X θ) (to-comm-η X θ)

module _ (a b : F-Alg₀) (morph : F-Alg₁ a b) where
  open F-Alg₀ a
  open F-Alg₀ b renaming ( X to Y ; θ to ρ )

  open F-Alg₁ morph

  pf : (x : F*₀ X)
     → f (to X θ x) ≡ to Y ρ (F*₁ f x)
  pf = 
    F*₀-ind X 
            (λ x → f (to X θ x) ≡ to Y ρ (F*₁ f x))  -- goal
            (λ x → refl)  -- η case
            (λ s t ind-hyp → 
              begin 
                f (to X θ (c (s , t)))
                  ≡⟨ refl ⟩ -- def. of "to X θ"
                f (θ (F₁ (to X θ) (s , t))) 
                  ≡⟨ refl ⟩ -- def. of "F₁"
                f (θ (s , to X θ ∘ t)) 
                  ≡⟨ comm (s , to X θ ∘ t) ⟩ -- use fact that θ is an alg. morph.
                ρ (F₁ f (s , to X θ ∘ t)) 
                  ≡⟨ refl ⟩ -- def. of "F₁"
                ρ (s , f ∘ to X θ ∘ t) 
                  -- use induction hypothesis
                  ≡⟨ cong (λ p → ρ (s , p)) (fun-ext (f ∘ to X θ ∘ t) (to Y ρ ∘ F*₁ f ∘ t) ind-hyp) ⟩
                ρ (s , to Y ρ ∘ F*₁ f ∘ t) 
                  ≡⟨ refl ⟩ -- def. of "to Y ρ"
                to Y ρ (F*₁ f (c (s , t))) ∎) 

  to₁ : F*-Alg₁ (to₀ a) (to₀ b)
  to₁ = mk-F-alg-morphism f pf

from : {X : Set} → (F*₀ X → X) → F₀ X → X
from {X} θ = θ ∘ c ∘ F₁ η

from₀ : F*-MonAlg₀ → F-Alg₀
from₀ (mk-F*-MonAlg X θ comm-μ comm-η) = mk-F-alg X (from θ)

module _ (a b : F*-MonAlg₀) (morph : F*-Alg₁ a b) where
  open F*-MonAlg₀ a
  open F*-MonAlg₀ b renaming ( X to Y ; θ to ρ )

  open F*-Alg₁ morph

  -- This proof essentially uses naturality of Fη and c and then uses
  -- the fact that f is an alg. morph.
  from₁ : F-Alg₁ (from₀ a) (from₀ b)
  from₁ = mk-F-alg-morphism f (comm ∘ c ∘ F₁ η)

-- Now we need to establish that the functors from and to form an
-- equivalence. We will only do this on the object part, ignoring the
-- equalities. For the morphisms, it holds trivially on the morphism
-- part. Also there we ignore the equalities.
module _ (alg : F-Alg₀) where
  open F-Alg₀ alg

  from₀-to : (x : F₀ X) → from (to X θ) x ≡ θ x
  from₀-to (s , t) = refl

module _ (monalg : F*-MonAlg₀) where
  open F*-MonAlg₀ monalg

  to₀-from₀ : (x : F*₀ X) → to X (from θ) x ≡ θ x
  to₀-from₀ = 
    F*₀-ind X 
            (λ x → to X (from θ) x ≡ θ x) -- goal
            comm-η -- η case
            (λ s t ind-hyp →
              begin
                to X (from θ) (c (s , t))
                  ≡⟨ refl ⟩ -- def. of "to (from θ)"
                from θ (s , to X (from θ) ∘ t)
                  ≡⟨ refl ⟩ -- def. of "from θ"
                θ (c (s , η ∘ to X (from θ) ∘ t))
                  -- apply induction hypothesis
                  ≡⟨ cong (λ x → θ (c (s , η ∘ x))) (fun-ext (to X (from θ) ∘ t) (θ ∘ t) ind-hyp) ⟩
                θ (c (s , η ∘ θ ∘ t)) -- See diagram below
                  ≡⟨ refl ⟩ 
                θ (F*₁ θ (c (s , η ∘ t)))
                  ≡⟨ comm-μ (c (s , η ∘ t)) ⟩
                θ (μ (c (s , η ∘ t)))
                  ≡⟨ refl ⟩
                θ (c (s , t)) ∎)

-- The last steps are justified by the following diagram. The top two
-- squares are, respectively, naturality of η (hence also of Fη),
-- naturality of c. The bottom square is the commutative of θ with
-- μ. Note that the bottom square holds only propositionally, the top
-- two squares are definitional equalities.

-- FF*X ------Fθ---> FX
--  |                |
--  Fη              Fη
--  |                |
--  v                v
-- FF*F*X --FF*θ--> FF*X
--  |                |
--  c                c
--  |                |
--  v                v
-- F*F*X ----F*θ--> F*X
--  |                |
--  μ                θ
--  |                |
--  v                v
-- F*X --------θ-->  X
