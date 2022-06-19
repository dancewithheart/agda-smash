{-# OPTIONS --without-K --safe #-}

module Data.Wedge where

open import Level
open import Data.Sum renaming
 ( _⊎_ to _+_
 ; swap to s-swap
 ; map to s-map
 ; inj₁ to left
 ; inj₂ to right
 )
open import Data.Product using (_×_; _,_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Function.Base using (id)

private
  variable
    lA lB lP lA' lB' lC lC' : Level
    A  : Set lA
    B  : Set lB
    A' : Set lA'
    B' : Set lB'
    C  : Set lC
    C' : Set lC'

{-

Wedge introduction rules:

A : Type   B Type
-------------------
nowhere : Wedge A B


A : Type   B Type   a : A
-------------------------
here a : Wedge A B


A : Type   B Type   b : B
-------------------------
there a : Wedge A B

-}
data Wedge {lA lB} (A : Set lA)(B : Set lB) : Set (lA ⊔ lB) where
  nowhere : Wedge A B
  here : (a : A) -> Wedge A B
  there : (b : B) -> Wedge A B

-- map

bimap : (f : A -> A') (g : B -> B') -> Wedge A B -> Wedge A' B'
bimap f g nowhere = nowhere
bimap f g (here a) = here (f a)
bimap f g (there b) = there (g b)

map : (f : A -> A') -> Wedge A B -> Wedge A' B
map f = bimap f id

map-left : (g : B -> B') -> Wedge A B -> Wedge A B'
map-left = bimap id

-- fold

{-
Wedge elimination rule

A : Type   B Type  C : Type
c: C   ac : A->C   bc: B->C
w: Wedge A B
-------------------
c : C

-}

fold : C -> (A -> C) -> (B -> C) -> Wedge A B -> C
fold c ac bc nowhere = c
fold c ac bc (here a) = ac a
fold c ac bc (there b) = bc b

biap : Wedge (A -> A') (B -> B') -> Wedge A B -> Wedge A' B'
biap (here f) (here a) = here (f a)
biap (there f) (there b) = there (f b)
biap _ = \ x -> nowhere

fromSum : A + B -> Wedge A B
fromSum (left a) = here a
fromSum (right b) = there b

fromWedge : Wedge A B -> Maybe (A + B)
fromWedge nowhere = nothing
fromWedge (here a) = just (left a)
fromWedge (there b) = just (right b)

swap : Wedge A B -> Wedge B A
swap nowhere = nowhere
swap (here a) = there a
swap (there b) = here b

Wedge-induction : {A : Set lA} {B : Set lB} (P : Wedge A B -> Set lP)
 -> P nowhere
 -> ((a : A) -> P (here a))
 -> ((b : B) -> P (there b))
 -> (w : Wedge A B) -> P w
Wedge-induction P pn _ _ nowhere = pn
Wedge-induction P _ ph _ (here a) = ph a
Wedge-induction P _ _ pt (there b) = pt b
