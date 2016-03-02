{-# OPTIONS --without-K #-}

module Container.Morphism where

open import lib.Basics
open import Container.Core

record ContHom (A B : Container) : Type0 where
  constructor mk-cont-hom
  open Container A
  open Container B renaming (Sh to Th ; Ps to Qs)
  field
    sh : Sh → Th
    ps : (s : Sh) → Qs (sh s) → Ps s

apply : {F G : Container} (α : ContHom F G) (X : Type0) → ⟦ F ⟧₀ X → ⟦ G ⟧₀ X
apply (mk-cont-hom sh ps) X (s , t) = sh s , t ∘ (ps s)

_‼_ : {F G : Container} (α : ContHom F G) {X : Type0} → ⟦ F ⟧₀ X → ⟦ G ⟧₀ X
_‼_ α {X} = apply α X
