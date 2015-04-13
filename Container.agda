-- Generalised containers
module Container where

open import Data.Product 
open import Relation.Binary.PropositionalEquality
open import Category
open import Data.Unit

infix 5 _◁_

record Container (C : Category) : Set₁ where
  constructor _◁_
  field
    Shapes    : Set
    Positions : Shapes → / C /

-- Functorial actions
module _ {C : Category} where
  -- Action on objects
  ⟦_⟧₀ : Container C → / C / → Set
  ⟦_⟧₀ (S ◁ P) X = Σ S (λ s → Category.hom C (P s) X)

  -- Action on morphisms
  ⟦_⟧₁ : {X Y : / C /} → (F : Container C) → Category.hom C X Y → ⟦ F ⟧₀ X → ⟦ F ⟧₀ Y
  ⟦_⟧₁ (S ◁ P) f (s , t) = (s , Category.comp C f t)

  -- Functor laws only hold strictly if id-unit-l and comp-assoc hold
  -- strictly.
  module _ (F : Container C) where
    ⟦id⟧₁=id : {X : / C /} → (x : ⟦ F ⟧₀ X) → ⟦ F ⟧₁ (Category.id C) x ≡ x
    ⟦id⟧₁=id (s , t) = cong (λ x → s , x) (Category.id-unit-l C)

    FgFf=Fgf : {X Y Z : / C /} → (g : Category.hom C Y Z) (f : Category.hom C X Y)
               (x : ⟦ F ⟧₀ X) → ⟦ F ⟧₁ g (⟦ F ⟧₁ f x) ≡ ⟦ F ⟧₁ (Category.comp C g f) x
    FgFf=Fgf g f (s , t) = cong (λ y → s , y) (Category.comp-assoc C g f t)

  module _ where
    open import FunExt

    ⟦_⟧ : Container C → Functor C Type
    ⟦ F ⟧ = record 
      { obj = ⟦ F ⟧₀ ; hom = ⟦ F ⟧₁ 
      ; id = λ X → fun-ext (⟦ F ⟧₁ (Category.id C)) 
                           (λ z → z) 
                           ( λ { (x , y) → cong (λ z → x , z) (Category.id-unit-l C) }) 
      ; comp = λ g f → fun-ext (⟦ F ⟧₁ (Category.comp C g f)) 
                               (λ z → ⟦ F ⟧₁ g (⟦ F ⟧₁ f z))
                               (λ { (x , h) → cong (λ z → x , z) (sym (Category.comp-assoc C g f h)) } )
      }

-- Composition of containers
_∘c_ : Container Type → Container Type → Container Type
(S ◁ P) ∘c (Q ◁ R) = (Σ Q (λ q → R q → S)) ◁ ( λ { (q , f) → Σ (R q) (λ r → P (f r)) })

-- Composition is indeed composition
module Composition-correctness (F G : Container Type) (X : Set) where
  open Container F renaming ( Shapes to S ; Positions to P )
  open Container G renaming ( Shapes to Q ; Positions to R )

  open import Function renaming ( _∘_ to _∘'_ )

  to : ⟦ F ⟧₀ (⟦ G ⟧₀ X) → ⟦ G ∘c F ⟧₀ X
  to (s , t) = (s , proj₁ ∘' t) , (λ { (p , r) → proj₂ (t p) r }) 

  from : ⟦ G ∘c F ⟧₀ X → ⟦ F ⟧₀ (⟦ G ⟧₀ X)
  from ((s , t) , u) = s , (λ p → (t p) , (λ r → u (p , r)))

  to-from : (x : ⟦ G ∘c F ⟧₀ X) → x ≡ to (from x)
  to-from ((_ , _) , _) = refl
  
  -- This holds by function extensionality, I guess.
  --from-to : (x : ⟦ F ⟧₀ (⟦ G ⟧₀ X)) → x ≡ from (to x)
  --from-to (s , t) = {!!}

Idc : Container Type
Idc = ⊤ ◁ (λ _ → ⊤)

-- Container morphisms
module _ {C : Category} (F G : Container C) where
  record ContainerMorphism : Set where
    constructor mk-cont-morphism
    
    open Container F renaming ( Shapes to S ; Positions to P )
    open Container G renaming ( Shapes to Q ; Positions to R )
  
    field
      f : S → Q
      g : (s : S) → Category.hom C (R (f s)) (P s)

  _‼_ : (α : ContainerMorphism) (X : / C /) → ⟦ F ⟧₀ X → ⟦ G ⟧₀ X
  _‼_ (mk-cont-morphism f g) X (s , t) = (f s) , (Category.comp C t (g s)) 

  -- Naturality:
  -- 
  -- F X -- α ‼ X --> G X
  --  |                |
  -- Ff               G f
  --  |                |
  --  V                V
  -- F y -- α ‼ Y --> G Y
  --
  naturality : (α : ContainerMorphism) (X Y : / C /) (f : Category.hom C X Y) (x : ⟦ F ⟧₀ X)
    → ⟦ G ⟧₁ f ((α ‼ X) x) ≡ (α ‼ Y) (⟦ F ⟧₁ f x)
  naturality (mk-cont-morphism a b) X Y f (s , t) = cong (λ x → a s , x) (Category.comp-assoc C f t (b s))

  -- Hence naturality holds strictly if associativity holds strictly in C.
module _ {C : Category} {F G : Container C} (α : ContainerMorphism F G) where
  open import FunExt

  ContainerNaturalTransformation : NaturalTransformation ⟦ F ⟧ ⟦ G ⟧
  ContainerNaturalTransformation = record
    { arr = λ X x → _‼_ F G α X x
    ; comm = λ X Y f → fun-ext (λ x →
                                    ContainerMorphism.f α (proj₁ x) ,
                                    Category.comp C f
                                    (Category.comp C (proj₂ x) (ContainerMorphism.g α (proj₁ x)))) 
                               (λ x →
                                    ContainerMorphism.f α (proj₁ x) ,
                                    Category.comp C (Category.comp C f (proj₂ x))
                                    (ContainerMorphism.g α (proj₁ x))) 
                               (λ x → naturality F G α X Y f x)
    }

-- TODO: Formalise this, alternative formulation of container morphisms
--   (f : S -> Q) × (g : (s : S) -> C(R (f s), P s))
-- ≃ (s : S) -> (q : Q) × C(R q, P s)
-- ≡ (s : S) -> [| Q ◁ R |] (P s)
