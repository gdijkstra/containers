module FunExt where

open import Relation.Binary.PropositionalEquality

postulate
  fun-ext : {A B : Set} → (f g : A → B) → ((x : A) → f x ≡ g x) → f ≡ g
