{-# OPTIONS --without-K #-}

open import Category hiding (_∘_)
open import Container

module FreeMonad (F : Container Type) where

open import Level
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

-- Aliases to make things a bit more readable.
private 
  F₀ : Set → Set
  F₀ = ⟦ F ⟧₀
  
  F₁ : {X Y : Set} → (X → Y) → (F₀ X → F₀ Y)
  F₁ = ⟦ F ⟧₁

  S : Set
  S = Container.Shapes F
  
  P : S → Set
  P = Container.Positions F

data F*₀ (X : Set) : Set where
  η : X → F*₀ X
  c : F₀ (F*₀ X) → F*₀ X

-- If we inline F₁, things should pass the termination checker.
{-# NO_TERMINATION_CHECK #-}
F*₀-elim : (X : Set) (Y : Set)
           (m-η : X → Y)
           (m-c : F₀ Y → Y)
          → F*₀ X → Y
F*₀-elim X Y m-η m-c (η x) = m-η x
F*₀-elim X Y m-η m-c (c x) = m-c (F₁ (F*₀-elim X Y m-η m-c) x)

-- Inlining everything means we pass the termination checker.
F*₀-ind : (X : Set) (Y : F*₀ X → Set)
          (m-η : (x : X) → Y (η x))
          (m-c : (s : S) (t : P s → F*₀ X)
                 (f : (p : P s) → Y (t p))
                → Y (c (s , t)))
        → (x : F*₀ X) → Y x
F*₀-ind X Y m-η m-c (η x) = m-η x
F*₀-ind X Y m-η m-c (c (s , t)) = m-c s t (λ p → F*₀-ind X Y m-η m-c (t p))
    
F*₁ : {X Y : Set} → (X → Y) → (F*₀ X → F*₀ Y)
F*₁ {X} {Y} f = F*₀-elim X (F*₀ Y) (η ∘ f) c

μ : {X : Set} → F*₀ (F*₀ X) → F*₀ X
μ {X} = F*₀-elim (F*₀ X) (F*₀ X) id c

-- The constructors are natural transformations, definitionally.
module _ (X Y : Set) (f : X → Y) where
  c-nat : (x : F₀ (F*₀ X)) → c (F₁ (F*₁ f) x) ≡ F*₁ f (c x)
  c-nat x = refl
  
  η-nat : (x : X) → η (f x) ≡ F*₁ f (η x)
  η-nat x = refl

-- F*₀ as a container:

-- Is this construction an instance of the general fixpoint
-- construction that translates binary containers into unary ones?
open import Data.Unit

S* : Set
S* = F*₀ ⊤

P* : S* -> Set
P* (η x) = ⊤
P* (c (s , t)) = Σ (P s) (λ i → P* (t i))

F*₀' : Set → Set
F*₀' X = Σ S* (λ s → P* s → X)

η* : {X : Set} → X → F*₀' X
η* x = (η tt) , (λ _ → x)

-- This I don't understand fully yet. It seems like one should be able to express this using some maps and stuff.
c* : {X : Set} → F₀ (F*₀' X) → F*₀' X
c* (s , t) = (c (s , (proj₁ ∘ t))) , (λ { (ps , ps') → proj₂ (t ps) ps' })

--match : {X : Set} → F*₀' X → X ⊔ 
open import Data.Sum

match* : {X : Set} → F*₀' X → X ⊎ F₀ (F*₀' X)
match* (η x , t)       = inj₁ (t tt)
match* (c (s , u) , t) = inj₂ (s , (λ ps → (u ps) , (λ z → t (ps , z))))

-- These now should follow straightforwardly from the above observations.
module _ (X : Set) (Y : Set)
         (m-η : X → Y)
         (m-c : F₀ Y → Y)
       where
  {-# NO_TERMINATION_CHECK #-}
  F*₀'-elim : F*₀' X → Y
  F*₀'-elim (η x , t) = m-η (t tt)
  F*₀'-elim (c (s , u) , t) = m-c (F₁ F*₀'-elim (s , (λ ps → u ps , (λ z → t (ps , z)))))

-- Inlining everything means we pass the termination checker.
module _ (X : Set) (Y : F*₀' X → Set)
          (m-η : (x : X) → Y (η* x))
          (m-c : (s : S) (t : P s → F*₀' X)
                 (f : (p : P s) → Y (t p))
                → Y (c* (s , t)))
       where
  {-# NO_TERMINATION_CHECK #-}
  F*₀'-ind : (x : F*₀' X) → Y x
  F*₀'-ind (η x , t) = m-η (t tt)
  F*₀'-ind (c (s , u) , t) = m-c s (λ z → u z , (λ x → t (z , x))) (λ p → F*₀'-ind (u p , (λ x → t (p , x)))) --m-c s ? (F₁ F*₀'-ind (s , (λ ps → u ps , (λ z → t (ps , z)))))

module _ (X : Set) where
 -- Of course this is now more or less meaningless. Once you get the
 -- induction principle, you get initiality. (Under what assumptions
 -- exactly?) So this proof is more or less superfluous, but neat
 -- nonetheless.
 iso-to : F*₀' X -> F*₀ X
 iso-to = F*₀'-elim X (F*₀ X) η c
  
 iso-from : F*₀ X -> F*₀' X
 iso-from = F*₀-elim X (F*₀' X) η* c*

 postulate
   funext : {A B : Set} (f g : A → B) → ((x : A) → f x ≡ g x) → f ≡ g

 to-from : (x : F*₀ X) → iso-to (iso-from x) ≡ x
 to-from = F*₀-ind X (λ x → iso-to (iso-from x) ≡ x) (λ x → refl) (λ s t f → cong (λ r → c (s , r)) (funext _ t f))

 from-to : (x : F*₀' X) → iso-from (iso-to x) ≡ x
 from-to = F*₀'-ind X (λ x → iso-from (iso-to x) ≡ x) (λ x → refl) (λ s t f → cong (λ r → c* (s , r)) (funext _ t f))
