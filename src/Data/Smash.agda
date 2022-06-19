{-# OPTIONS --without-K --safe #-}

module Data.Smash where

open import Level
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

data Smash {lA lB} (A : Set lA) (B : Set lB) : Set (lA ⊔ lB) where
  nada  :           Smash A B
  smash : A -> B -> Smash A B

fromSmash : Smash A B -> Maybe (A × B)
fromSmash nada = nothing
fromSmash (smash a b) = just (a , b)

-- projections

smashFst : Smash A B -> Maybe A
smashFst nada = nothing
smashFst (smash a b) = just a

smashSnd : Smash A B -> Maybe B
smashSnd nada = nothing
smashSnd (smash a b) = just b

-- injection

fromProduct : A × B -> Smash A B
fromProduct (a , b) = smash a b

toSmash : Maybe (A × B) -> Smash A B
toSmash (just (a , b)) = smash a b
toSmash nothing = nada

smashDiag : Maybe A -> Smash A A
smashDiag (just a) = smash a a
smashDiag nothing = nada

smashDiag' : A -> Smash A A
smashDiag' a = smash a a

-- swap

swap : Smash A B -> Smash B A
swap nada = nada
swap (smash a b) = smash b a

-- map

bimap : (f : A -> A') (g : B -> B') -> Smash A B -> Smash A' B'
bimap f g nada = nada
bimap f g (smash a b) = smash (f a) (g b)

map : (f : A -> A') -> Smash A B -> Smash A' B
map f = bimap f id

map-left : (g : B -> B') -> Smash A B -> Smash A B'
map-left = bimap id

-- fold

fold : C -> (A -> B -> C) -> Smash A B -> C
fold c abc nada = c
fold c abc (smash a b) = abc a b

-- bind

bind : Smash A B -> (f : (A × B) -> Smash A' B') -> Smash A' B'
bind nada f = nada
bind (smash a b) f = f (a , b)

-- ap

ap : Smash (A -> A') (B -> B') -> Smash A B -> Smash A' B'
ap nada = \ x -> nada
ap (smash f g) = bimap f g

-- assocciativity

reassocLR : Smash (Smash A B) C -> Smash A (Smash B C)
reassocLR (smash (smash a b) c) = smash a (smash b c)
reassocLR _ = nada

reassocRL : Smash (Smash A B) C -> Smash (Smash A B) C
reassocRL (smash (smash a b) c) = smash (smash a b) c
reassocRL _ = nada

Smash-Induction : {A : Set lA} {B : Set lB} (P : Smash A B -> Set lP)
  -> P nada
  -> ((a : A) -> (b : B) -> P (smash a b))
  -> (s : Smash A B) -> P s
Smash-Induction P pn ps nada = pn
Smash-Induction P pn ps (smash a b) = ps a b
