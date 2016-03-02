{-# OPTIONS --without-K #-}

open import Category

module Generalised.Morphism (𝓒 : Cat) where

open Cat 𝓒

open import lib.Basics
open import Generalised.Core 𝓒

record ContHom (A B : Container) : Type0 where
  constructor mk-cont-hom
  open Container A
  open Container B renaming (Sh to Th ; Ps to Qs)
  field
    sh : Sh → Th
    ps : (s : Sh) → 𝓒 [ Qs (sh s) , Ps s ]

apply : {F G : Container} (α : ContHom F G) (X : / 𝓒 /) → ⟦ F ⟧₀ X → ⟦ G ⟧₀ X
apply (mk-cont-hom sh ps) X (s , t) = (sh s , comp t (ps s))

_‼_ : {F G : Container} (α : ContHom F G) {X : / 𝓒 /} → ⟦ F ⟧₀ X → ⟦ G ⟧₀ X
_‼_ α {X} = apply α X
