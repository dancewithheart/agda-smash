{-# OPTIONS --without-K --safe #-}

module Data.Can where

open import Level
open import Data.Product using (_,_) renaming (_×_ to _*_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum renaming
 ( _⊎_ to _+_
 ; swap to s-swap
 ; inj₁ to left
 ; inj₂ to right
 )

private
  variable
    lA lB lP lA' lB' lC : Level
    A  : Set lA
    B  : Set lB
    A' : Set lA'
    B' : Set lB'
    C  : Set lC

{-
Can introduction rules:

A : Type   B Type
-------------------
non : Wedge A B


A : Type   B Type   a : A
-------------------------
one a : Wedge A B


A : Type   B Type   b : B
--------------------------
eno b : Wedge A B


A : Type   B Type   a : A   b : B
---------------------------------
two a b : Wedge A B

-}
data Can (A : Set lA)(B : Set lB) : Set (lA ⊔ lB) where
  non : Can A B
  one : A      -> Can A B
  eno :      B -> Can A B
  two : A -> B -> Can A B

fold : C -> (A -> C) -> (B -> C) -> (A -> B -> C) -> Can A B -> C
fold c _ _ _ non         = c
fold c ac _ _ (one a)    = ac a
fold c _ bc _ (eno b)    = bc b
fold c _ _ abc (two a b) = abc a b

foldWithMerge : C -> (A -> C) -> (B -> C) -> (C -> C -> C) -> Can A B -> C
foldWithMerge c _ _ _ non         = c
foldWithMerge c ac _ _ (one a)    = ac a
foldWithMerge c _ bc _ (eno b)    = bc b
foldWithMerge _ ac bc m (two a b) = m (ac a) (bc b)

-- associativity

reassocLR : Can (Can A B) C -> Can A (Can B C)
reassocLR non               = non
reassocLR (one non)         = non
reassocLR (one (one a))     = one a
reassocLR (one (eno b))     = eno (one b)
reassocLR (one (two a b))   = two a (one b)
reassocLR (eno c)           = eno (eno c)
reassocLR (two non c)       = eno (eno c)
reassocLR (two (one a) c)   = two a (eno c)
reassocLR (two (eno b) c)   = eno (two b c)
reassocLR (two (two a b) c) = two a (two b c)

reassocRL : Can A (Can B C) -> Can (Can A B) C
reassocRL non               = non
reassocRL (one a)           = one (one a)
reassocRL (eno non)         = non
reassocRL (eno (one b))     = one (eno b)
reassocRL (eno (eno c))     = eno c
reassocRL (eno (two b c))   =  two (eno b) c
reassocRL (two a non)       = one (one a)
reassocRL (two a (one b))   = one (two a b)
reassocRL (two a (eno c))   = two (one a) c
reassocRL (two a (two b c)) = two (two a b) c

-- commutativity / symmetry

swap : Can A B -> Can B A
swap non       = non
swap (one a)   = eno a
swap (eno b)   = one b
swap (two a b) = two b a

-- distributivity

distributeCan : Can (A * B) C -> ((Can A C) * (Can B C))
distributeCan non             = (non , non)
distributeCan (one (a , b))   = (one a) , (one b)
distributeCan (eno c)         = (eno c) , (eno c)
distributeCan (two (a , b) c) = (two a c) , (eno c)

codistributeCan : (Can A C) + (Can B C) -> Can (A + B) C
codistributeCan (left  non)       = non
codistributeCan (left  (one a))   = one (left a)
codistributeCan (left  (eno c))   = eno c
codistributeCan (left  (two a c)) = two (left a) c
codistributeCan (right non)       = non
codistributeCan (right (one b))   = one (right b)
codistributeCan (right (eno c))   = eno c
codistributeCan (right (two b c)) = two (right b) c

bimap : (A -> A') -> (B -> B') -> Can A B -> Can A' B'
bimap f g non = non
bimap f g (one a) = one (f a)
bimap f g (eno b) = eno (g b)
bimap f g (two a b) = two (f a) (g b)

bipure : A -> B -> Can A B
bipure = two

biap : Can (A -> A') (B -> B') -> Can A B -> Can A' B'
biap (one fa)    (one a)   = one (fa a)
biap (one fa)    (two a b) = one (fa a)
biap (eno fb)    (eno b)   = eno (fb b)
biap (eno fb)    (two a b) = eno (fb b)
biap (two fa fb) (two a b) = two (fa a) (fb b)
biap (two fa fb) (one a)   = one (fa a)
biap (two fa fb) (eno b)   = eno (fb b)
biap _ _                   = non

-- TODO add to Haskell
canProduct : Maybe A -> Maybe B -> Can A B
canProduct (just a) (just b) = two a b
canProduct (just a) nothing  = one a
canProduct nothing (just b)  = eno b
canProduct nothing nothing   = non

-- TODO add to Haskell
canSum : Maybe A + Maybe B -> Can A B
canSum (left (just a))  = one a
canSum (left nothing)   = non
canSum (right (just b)) = eno b
canSum (right nothing)  = non

-- TODO add to Haskell
canSum2 : Maybe (A + B) -> Can A B
canSum2 (just (left a))  = one a
canSum2 (just (right b)) = eno b
canSum2 nothing          = non

canFst : Can A B -> Maybe A
canFst (one a)   = just a
canFst (two a b) = just a
canFst _         = nothing

canSnd : Can A B -> Maybe B
canSnd (eno b)   = just b
canSnd (two a b) = just b
canSnd _         = nothing

fromProduct : A * B -> Can A B
fromProduct (a , b) = two a b

fromSum : A + B -> Can A B
fromSum (left  a) = one a
fromSum (right b) = eno b

Can-Induction : {A : Set lA} {B : Set lB} (P : Can A B -> Set lP)
  -> P non
  -> ((a : A) -> P (one a))
  -> ((b : B) -> P (eno b))
  -> ((a : A) -> (b : B) -> P (two a b))
  -> (s : Can A B) -> P s
Can-Induction P pn po pe pt non       = pn
Can-Induction P pn po pe pt (one a)   = po a
Can-Induction P pn po pe pt (eno b)   = pe b
Can-Induction P pn po pe pt (two a b) = pt a b

canCurry : (Can A B -> Maybe C) -> Maybe A -> Maybe B -> Maybe C
canCurry f (just a) (just b) = f (two a b)
canCurry f (just a) nothing  = f (one a)
canCurry f nothing  (just b) = f (eno b)
canCurry f nothing  nothing  = f non

canUncurry : (Maybe A -> Maybe B -> Maybe C) -> Can A B -> Maybe C
canUncurry f non       = f nothing  nothing
canUncurry f (one a)   = f (just a) nothing
canUncurry f (eno b)   = f nothing  (just b)
canUncurry f (two a b) = f (just a) (just b)
