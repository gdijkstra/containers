-- Finitary containers are ω-cocontinuous
module Finitary.Cocontinuity where

open import lib.Basics
open import lib.types.Nat
open import Finitary.Fin

max-ℕ : ℕ → ℕ → ℕ
max-ℕ O y = y
max-ℕ (S x) O = S x
max-ℕ (S x) (S y) = S (max-ℕ x y)

module _
  -- Cochain (X,i)
  (X : (n : ℕ) → Type0)
  (i : (n : ℕ) → X n → X (S n))
  -- Finitary functor F X :≡ Fin k → X
  (k : ℕ)
  -- Colimit of (X,i)
  (A : Type0)
  (g : (n : ℕ) → X n → A)
  (p : (n : ℕ) → g (S n) ∘ i n == g n)
  -- Recursion principle of A
  (A-rec :
    (Z : Type0)
    (a : (n : ℕ) → X n → Z)
    (b : (n : ℕ) → a (S n) ∘ i n == a n)
    → A → Z)
  -- Colimit of (FX,Fi)
  (B : Type0)
  (h : (n : ℕ) → (Fin k → X n) → B)
  (q : (n : ℕ) → h (S n) ∘ (λ f → i n ∘ f) == h n)
  -- Recursion principle of B
  (B-rec :
    (Z : Type0)
    (a : (n : ℕ) → (Fin k → X n) → Z)
    (b : (n : ℕ) → a (S n) ∘ (λ f → i n ∘ f) == a n)
    → B → Z)
  where

  max'' : {n m : ℕ} → X n → X m → X (max-ℕ n m)
  max'' {O} {m} x y = y
  max'' {S n} {O} x y = x
  max'' {S n} {S m} x y = {!i (max-ℕ n m)!}

  max' : A → A → A
  max' = A-rec (A → A) (λ n x → A-rec A (λ m y → g {!!} {!!}) {!!}) {!!}

  max : (Fin k → A) → A
  max f = {!!}
  
  to : (Fin k → A) → B
  to = {!!}

  from : B → (Fin k → A)
  from = B-rec (Fin k → A) (λ n x y → g n (x y)) (λ n → λ= (λ x → λ= (λ y → app= (p n) (x y))))
