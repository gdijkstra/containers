module Category where

open import Relation.Binary.PropositionalEquality

record Category : Set₂ where
  field
    obj        : Set₁
    hom        : obj → obj → Set
    id         : {X : obj} → hom X X
    comp       : {X Y Z : obj} → hom Y Z → hom X Y → hom X Z
    comp-assoc : {X Y Z W : obj} → (h : hom Z W) (g : hom Y Z) (f : hom X Y)
               → comp h (comp g f) ≡ comp (comp h g) f
    id-unit-l  : {X Y : obj} {t : hom X Y} → comp id t ≡ t
    -- id unit

/_/ : Category → Set₁
/ C / = Category.obj C

Type : Category
Type = record 
       { obj        = Set 
       ; hom        = λ x y → x → y
       ; id         = λ x → x 
       ; comp       = λ g f x → g (f x) 
       ; comp-assoc = λ h g f → refl
       ; id-unit-l  = refl
       }

record Functor (C D : Category) : Set₁ where
  field
    obj : / C / → / D /
    hom : {X Y : / C /} → (Category.hom C X Y) → (Category.hom D (obj X) (obj Y))
    id : (X : / C /) → hom {X} {X} (Category.id C {X}) ≡ Category.id D {obj X}
    comp : {X Y Z : / C /} → (g : Category.hom C Y Z) (f : Category.hom C X Y) 
         → hom (Category.comp C g f) ≡ Category.comp D (hom g) (hom f)

module _ {C D : Category} (F G : Functor C D) where
  record NaturalTransformation : Set₁ where
    field
      arr : (X : / C /) → Category.hom D (Functor.obj F X) (Functor.obj G X)
      comm : (X Y : / C /) (f : Category.hom C X Y)
           → Category.comp D (Functor.hom G f) (arr X)  ≡ Category.comp D (arr Y) (Functor.hom F f)

  -- ≡-NatTrans :
  --   (arr₀ arr₁ : (X : / C /) → Category.hom D (Functor.obj F X) (Functor.obj G X))
  --   (comm₀ : (X Y : / C /) (f : Category.hom C X Y)
  --                → Category.comp D (Functor.hom G f) (arr₀ X)  ≡ Category.comp D (arr₀ Y) (Functor.hom F f))
  --   (comm₁ : (X Y : / C /) (f : Category.hom C X Y)
  --                → Category.comp D (Functor.hom G f) (arr₁ X)  ≡ Category.comp D (arr₁ Y) (Functor.hom F f))
  --   → (p : arr₀ ≡ arr₁)
  --   → {!!}
  --   → _≡_ {A = NaturalTransformation} (record { arr = arr₀ ; comm = comm₀ }) (record { arr = arr₁ ; comm = subst {!!} p comm₁ })
  -- ≡-NatTrans arr₀ arr₁ comm₀ comm₁ p q = {!!}
