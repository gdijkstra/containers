-- The goal of this development is to show the equivalence of F-Alg and F*-MonAlg.

module FreeMonad (S : Set) (P : S → Set) where

open import Level
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

-- Action on objects.
F₀ : Set → Set
F₀ X = Σ S (λ s → P s → X)

-- Action on morphisms.
F₁ : {X Y : Set} → (X → Y) → (F₀ X → F₀ Y)
F₁ f (s , t) = s , f ∘ t

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

postulate
  fun-ext : {A B : Set} → (f g : A → B) → ((x : A) → f x ≡ g x) → f ≡ g

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

-- F*₀ as a container:
-- _* : Container → Container
-- C * = S* ▷ P*
--   where
--     open Container.Container C

--     S* : Type0
--     S* = Free C ⊤

--     P* : S* → Type0
--     P* (ret tt) = ⊤
--     P* (roll (s , u)) = Σ (Positions s) λ i → P* (u i)

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
