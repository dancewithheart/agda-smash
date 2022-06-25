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
  nowhere :           Wedge A B
  here    : A ->      Wedge A B
  there   :      B -> Wedge A B

{-
Wedge elimination rule

A : Type   B Type  C : Type
c: C   ac : A->C   bc: B->C
w: Wedge A B
-------------------
c : C

-}
fold : C
    -> (A -> C)
    -> (B -> C)
    -> Wedge A B -> C
fold c ac bc nowhere = c
fold c ac bc (here a) = ac a
fold c ac bc (there b) = bc b

-- Bifunctor ops

bimap : (f : A -> A') (g : B -> B')
     -> Wedge A B -> Wedge A' B'
bimap f g nowhere = nowhere
bimap f g (here a) = here (f a)
bimap f g (there b) = there (g b)

map-right : (f : A -> A')
         -> Wedge A B -> Wedge A' B
map-right f = bimap f id

map-left : (g : B -> B')
        -> Wedge A B -> Wedge A B'
map-left = bimap id

-- BiApplicative (no bipure)

biap : Wedge (A -> A') (B -> B')
    -> Wedge A B -> Wedge A' B'
biap (here f) (here a) = here (f a)
biap (there f) (there b) = there (f b)
biap _ = \ x -> nowhere

-- Wedge commutativity / symmetry

swap : Wedge A B -> Wedge B A
swap nowhere = nowhere
swap (here a) = there a
swap (there b) = here b

-- Wedge associativity

reassocLR : Wedge (Wedge A B) C -> Wedge A (Wedge B C)
reassocLR (there c) = there (there c)
reassocLR (here (there b)) = there (here b)
reassocLR (here (here a)) = here a
reassocLR (here nowhere) = nowhere
reassocLR nowhere = nowhere

reassocRL : Wedge A (Wedge B C) -> Wedge (Wedge A B) C
reassocRL nowhere = nowhere
reassocRL (here a) = here (here a)
reassocRL (there nowhere) = nowhere
reassocRL (there (here b)) = here (there b)
reassocRL (there (there c)) = there c

-- conversions

fromSum : A + B -> Wedge A B
fromSum (left a) = here a
fromSum (right b) = there b

quotWedge : (Maybe A) + (Maybe B) -> Wedge A B
quotWedge (left (just a)) = here a
quotWedge (left nothing) = nowhere
quotWedge (right (just b)) = there b
quotWedge (right nothing) = nowhere

-- collapses both nothing into single nowhere
toWedge : Maybe (A + B) -> Wedge A B
toWedge (just (left a)) = here a
toWedge (just (right b)) = there b
toWedge nothing = nowhere

fromWedge : Wedge A B -> Maybe (A + B)
fromWedge nowhere = nothing
fromWedge (here a) = just (left a)
fromWedge (there b) = just (right b)

-- projections

fromHere : Wedge A B -> Maybe A
fromHere (here a) = just a
fromHere _ = nothing

fromThere : Wedge A B -> Maybe B
fromThere (there b) = just b
fromThere _ = nothing

-- injections

wedgeLeft : Maybe A -> Wedge A B
wedgeLeft (just a) = here a
wedgeLeft nothing = nowhere

wedgeRight : Maybe B -> Wedge A B
wedgeRight (just b) = there b
wedgeRight nothing = nowhere

-- distributivity over product

distributeWedge : Wedge (A × B) C -> (Wedge A C × Wedge B C)
distributeWedge nowhere = (nowhere , nowhere)
distributeWedge (here (a , b)) = (here a , here b)
distributeWedge (there c) = (nowhere , there c)

codistributeWedge : (Wedge A C × Wedge B C) -> Wedge (A × B) C
codistributeWedge (nowhere , nowhere) = nowhere
codistributeWedge (nowhere , here b) = nowhere
codistributeWedge (nowhere , there c) = there c
codistributeWedge (here a , nowhere) = nowhere
codistributeWedge (here a , here b) = here (a , b)
codistributeWedge (here a , there c) = there c
codistributeWedge (there c , nowhere) = there c
codistributeWedge (there c , here b) = there c
codistributeWedge (there c1 , there c2) = there c1 -- can choose c2

Wedge-induction : {A : Set lA} {B : Set lB} (P : Wedge A B -> Set lP)
 -> P nowhere
 -> ((a : A) -> P (here a))
 -> ((b : B) -> P (there b))
 -> (w : Wedge A B) -> P w
Wedge-induction P pn _ _ nowhere = pn
Wedge-induction P _ ph _ (here a) = ph a
Wedge-induction P _ _ pt (there b) = pt b
