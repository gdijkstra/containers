{-# OPTIONS --without-K #-}

open import Category
open import Container

-- F-algebras, for some F : Type -> Type. Works for any functor, but I
-- don't feel like defining functors just yet.

module Algebras (F : Container Type) where

open import Data.Product
open import Relation.Binary.PropositionalEquality

obj : Set₁
obj = Σ Set (λ X → ⟦ F ⟧₀ X → X) 

hom : obj → obj → Set
hom (X , θ) (Y , ρ) = Σ (X → Y) (λ f → (x : ⟦ F ⟧₀ X) → f (θ x) ≡ ρ (⟦ F ⟧₁ f x))

id : {X : obj} → hom X X
id = (λ x → x) , (λ x → refl) 

open ≡-Reasoning

comp : {X Y Z : obj} → hom Y Z → hom X Y → hom X Z
comp {X , θ} {Y , ρ} {Z , χ} (g , comm₀) (f , comm₁) = 
  (λ x → g (f x))
  , (λ x → begin
             g (f (θ x)) 
           ≡⟨ cong g (comm₁ x) ⟩
             g (ρ (⟦ F ⟧₁ f x))
           ≡⟨ comm₀ (⟦ F ⟧₁ f x) ⟩
             χ (⟦ F ⟧₁ g (⟦ F ⟧₁ f x))
           ≡⟨ cong χ (FgFf=Fgf F g f x) ⟩
             χ (⟦ F ⟧₁ (λ x₁ → g (f x₁)) x)
           ∎)

cong-id : {A : Set} {x y : A} → (p : x ≡ y) → cong (λ x₁ → x₁) p ≡ p
cong-id refl = refl

trans-unit-r : {A : Set} {x y : A} → (p : x ≡ y) → trans p refl ≡ p
trans-unit-r refl = refl

-- We postulate these laws for the time being.
postulate
  id-unit-l : {X Y : obj} {t : hom X Y} → comp {X} {Y} {Y} id t ≡ t

-- id-unit-l {X , θ} {Y , ρ} {f , comm} = 
--   cong (λ p → f , p) 
--        (begin
--          (λ x → trans (cong (λ x₁ → x₁) (comm x)) refl)
--        ≡⟨ {!cong!} ⟩ -- here we need fun-ext it seems
--          (λ x → trans (comm x) refl)
--        ≡⟨ {!!} ⟩ -- here we need fun-ext it seems
--          (λ x → comm x)
--        ≡⟨ refl ⟩ 
--          comm
--        ∎)

postulate
  comp-assoc : {X Y Z W : obj} (h : hom Z W) (g : hom Y Z) (f : hom X Y) 
             → comp {X} {Z} {W} h (comp {X} {Y} {Z} g f) ≡ comp {X} {Y} {W} (comp {Y} {Z} {W} h g) f
-- comp-assoc {X , θ₀} {Y , θ₁} {Z , θ₂} {W , θ₃} (h , comm₂) (g , comm₁) (f , comm₀) = 
--   cong (λ p → (λ x → h (g (f x))) , p) {!!}


F-Alg : Category
F-Alg = record 
        { obj = obj 
        ; hom = hom
        ; id = id
        ; comp = λ {X} {Y} {Z} → comp {X} {Y} {Z}
        ; comp-assoc = λ {X} {Y} {Z} {W} → comp-assoc {X} {Y} {Z} {W}
        ; id-unit-l = λ {X} {Y} {t} → id-unit-l {X} {Y} {t}
        }

