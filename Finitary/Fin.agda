{-# OPTIONS --without-K #-}

-- Finite types
module Finitary.Fin where

open import lib.Base
open import lib.types.Nat
open import lib.types.Coproduct

data Fin : ℕ → Type0 where
  fZ : {n : ℕ} → Fin (S n)
  fS : {n : ℕ} → Fin n → Fin (S n)

finl : {n m : ℕ} → Fin n → Fin (n + m)
finl fZ = fZ
finl (fS n) = fS (finl n)

finr : {n m : ℕ} → Fin m → Fin (n + m)
finr {O} x = x
finr {S n} x = fS (finr {n} x)

data PlusView : {n m : ℕ} → Fin (n + m) → Type0 where
  inl : {n m : ℕ} (i : Fin n) → PlusView {n} {m} (finl i)
  inr : {n m : ℕ} (i : Fin m) → PlusView {n} {m} (finr {n} i)

plusView : {n m : ℕ} → (i : Fin (n + m)) → PlusView {n} {m} i
plusView {O} x = inr x
plusView {S n} fZ = inl fZ
plusView {S n} (fS x) with plusView {n} x
plusView {S n} (fS ._) | inl i = inl (fS i)
plusView {S n} (fS ._) | inr i = inr i

fpluscase : {n m : ℕ} → Fin (n + m) → Fin n ⊔ Fin m
fpluscase {n} {m} x with plusView {n} {m} x
fpluscase ._ | inl i = inl i
fpluscase ._ | inr i = inr i

_*_ : ℕ → ℕ → ℕ
O * m = 0
S n * m = m + (n * m)

fpair : {n m : ℕ} → Fin n → Fin m → Fin (n * m)
fpair {O} ()
fpair {S n} {m} fZ     y = finl {m} {n * m} y
fpair {S n} {m} (fS x) y = finr {m} {n * m} (fpair x y)

data PairView : {n m : ℕ} → Fin (n * m) → Type0 where
  pair : {n m : ℕ} (i : Fin n) (j : Fin m) → PairView {n} {m} (fpair i j)

pairView : {n m : ℕ} → (i : Fin (n * m)) → PairView {n} {m} i
pairView {O} ()
pairView {S n} {m} i with plusView {m} {n * m} i
pairView {S n} {m} ._ | inl j = pair fZ j
pairView {S n} {m} ._ | inr j with pairView {n} {m} j
pairView {S n} ._ | inr ._ | pair i j = pair (fS i) j

ffst : {n m : ℕ} → Fin (n * m) → Fin n
ffst {n} {m} x with pairView {n} {m} x
ffst .(fpair i j) | pair i j = i

fsnd : {n m : ℕ} → Fin (n * m) → Fin m
fsnd {n} {m} x with pairView {n} {m} x
fsnd .(fpair i j) | pair i j = j

-- Family of finite types is basically a (finite) list of numbers.
sum : (A : ℕ) (B : Fin A → ℕ) → ℕ
sum O B = 0
sum (S A) B = B fZ + sum A (B ∘ fS)

prod : (A : ℕ) (B : Fin A → ℕ) → ℕ
prod O B = 0
prod (S A) B = B fZ * prod A (B ∘ fS)

Σ-Fin : (A : ℕ) (B : Fin A → ℕ) → Type0
Σ-Fin A B = Fin (sum A B)

Π-Fin : (A : ℕ) (B : Fin A → ℕ) → Type0
Π-Fin A B = Fin (prod A B)

fdpair :
  (A : ℕ) (B : Fin A → ℕ)
  (i : Fin A) (j : Fin (B i))
  → Σ-Fin A B
fdpair O     B i      j = i
fdpair (S A) B fZ     j = finl j
fdpair (S A) B (fS i) j = finr {B fZ} {sum A (B ∘ fS)} (fdpair A (λ z → B (fS z)) i j)

data SigmaView :
  (A : ℕ) (B : Fin A → ℕ) → Σ-Fin A B → Type0 where
  dpair : (A : ℕ) (B : Fin A → ℕ) (i : Fin A) (j : Fin (B i)) → SigmaView A B (fdpair A B i j)
  
sigmaView : (A : ℕ) (B : Fin A → ℕ) → (x : Σ-Fin A B) → SigmaView A B x
sigmaView O B ()
sigmaView (S A) B x with plusView {B fZ} {sum A (B ∘ fS)}  x
sigmaView (S A) B ._ | inl i = dpair (S A) B fZ i
sigmaView (S A) B ._ | inr j with sigmaView A (B ∘ fS) j
sigmaView (S A) B ._ | inr ._ | dpair .A ._ i j = dpair (S A) B (fS i) j 

fdfst : (A : ℕ) (B : Fin A → ℕ) → Σ-Fin A B → Fin A
fdfst A B x with sigmaView A B x
fdfst A B .(fdpair A B i j) | dpair .A .B i j = i

fdsnd : (A : ℕ) (B : Fin A → ℕ) → (i : Σ-Fin A B) → Fin (B (fdfst A B i))
fdsnd A B i with sigmaView A B i
fdsnd A B .(fdpair A B i j) | dpair .A .B i j = j

fsigmacase : (A : ℕ) (B : Fin A → ℕ) (i : Σ-Fin A B) → Σ (Fin A) (λ j → Fin (B j))
fsigmacase A B i with sigmaView A B i
fsigmacase A B .(fdpair A B i j) | dpair .A .B i j = i , j

