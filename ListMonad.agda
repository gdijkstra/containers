module ListMonad where

open import Container
open import Category
open import Monad
open import Data.Product
open import Data.Nat
open import Data.Fin hiding (_+_ ; compare ; _<_)

ListContainer : Container Type
ListContainer = ℕ ◁ Fin

-- Agda doesn't see this as being structurally recursive.
-- sum : Σ ℕ (λ n → Fin n → ℕ) → ℕ
-- sum (zero  , f) = zero
-- sum (suc n , f) = f zero + sum (n , (λ x → f (suc x)))

fold-fin-list : {X : Set} 
              → X
              → (ℕ → X → X)
              → (n : ℕ) → (Fin n → ℕ) → X
fold-fin-list e op zero f = e
fold-fin-list e op (suc n) f = op (f zero) (fold-fin-list e op n (λ x → f (suc x)))

nil : Fin 0 → ℕ
nil ()

cons : ℕ → (n : ℕ) (f : Fin n → ℕ) → (Fin (suc n) → ℕ)
cons x n f zero = x
cons x n f (suc k) = f k

elim-fin-list : {X : (n : ℕ) (f : Fin n → ℕ) → Set}
              → X 0 (λ ())
              → ((k : ℕ) →
                   (n : ℕ) (f : Fin n → ℕ) → X n f → X (suc n) (cons k n f))
              → (n : ℕ) (f : Fin n → ℕ) → X n f
elim-fin-list mn mc zero f = {!!} -- This is problematic, because functions out of ⊥ aren't unique.
elim-fin-list mn mc (suc n) f = {!!}

sum : (n : ℕ) → (Fin n → ℕ) → ℕ
sum = fold-fin-list 0 _+_

--  sum zero     f = zero
--  sum (suc n)  f = f zero + sum n (λ x → f (suc x))

finl : {m n : ℕ} -> Fin m -> Fin (m + n)
finl zero    = zero
finl (suc i) = suc (finl i)

finr : {m n : ℕ} -> Fin n -> Fin (m + n)
finr {zero}  i = i
finr {suc m} i = suc (finr {m} i)

data PlusView : {m n : ℕ} -> Fin (m + n) -> Set where
  inl : {m n : ℕ} -> (i : Fin m) -> PlusView {m} {n} (finl i)
  inr : {m n : ℕ} -> (i : Fin n) -> PlusView {m} {n} (finr {m} i)

plusView : {m n : ℕ} -> (i : Fin (m + n)) -> PlusView {m} {n} i
plusView {zero}   i       = inr i
plusView {suc m} zero     = inl (zero {m})
plusView {suc m} (suc i) with plusView {m} i
plusView {suc m} (suc ._) | (inl j) = inl {suc m} (suc j)
plusView {suc m} (suc ._) | (inr j) = inr j

open import Data.Sum

split : (m n : ℕ) → Fin (m + n) → Fin m ⊎ Fin n
split m n z with plusView {m} {n} z
split m n .(finl {m} i) | inl i = inj₁ i
split m n .(finr {m} i) | inr i = inj₂ i

div : (n : ℕ) (f : Fin n → ℕ) → Fin (sum n f) → Σ (Fin n) (λ y → Fin (f y))
div zero f ()
div (suc k) f z with plusView {f zero} {fold-fin-list zero _+_ k (λ z₁ → f (suc z₁))} z
div (suc k) f .(finl i) | inl i = zero , i
div (suc k) f .(finr {f zero} i) | inr i with div k (λ z → f (suc z)) i
div (suc k) f .(finr i) | inr i | a , b = suc a , b

-- Inverse to div
vid : (n : ℕ) (f : Fin n → ℕ) → (y : Fin n) (x : Fin (f y)) → Fin (sum n f)
vid ._ f zero x = finl x
vid ._ f (suc y) x = finr {f zero} (vid _ (λ x₁ → f (suc x₁)) y x)

-- Showing that this yields an iso appears to be painful because of the "with" clauses.

ListMonad : ContainerMonad ListContainer
ListMonad = mk-cont-monad 1 (λ x → sum (proj₁ x) (proj₂ x)) (λ { (n , f) x → div n f x })

