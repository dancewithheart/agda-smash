{-# OPTIONS --without-K --safe #-}

module Data.Smash where

open import Level
open import Data.Product using (_×_; _,_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Function.Base using (id)
open import Data.Wedge using (Wedge; nowhere; here; there)

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

-----------------
nada : Smash A B

a : A   b : B
----------------------
smash a b : Smash A B

-}
data Smash {lA lB} (A : Set lA) (B : Set lB) : Set (lA ⊔ lB) where
  nada  :           Smash A B
  smash : A -> B -> Smash A B

{-
Smash introduction rules

nothing : Maybe A   nothing : Maybe B
-------------------------------------
nada : Smash A B


just a: Maybe A   just b : Maybe B
---------------------------------
smash a b : Smash A B

alternatively:

just (a,b): Maybe A * B
-----------------------
smash a b : Smash A B

-}
smashProduct : Maybe A -> Maybe B -> Smash A B
smashProduct (just a) (just b) = smash a b
smashProduct _ _ = nada

toSmash : Maybe (A × B) -> Smash A B
toSmash (just (a , b)) = smash a b
toSmash nothing = nada

fold : C -> (A -> B -> C) -> Smash A B -> C
fold c abc nada = c
fold c abc (smash a b) = abc a b

-- commutativity / symmetry

swap : Smash A B -> Smash B A
swap nada = nada
swap (smash a b) = smash b a

-- assocciativity

reassocLR : Smash (Smash A B) C -> Smash A (Smash B C)
reassocLR (smash (smash a b) c) = smash a (smash b c)
reassocLR _ = nada

reassocRL : Smash (Smash A B) C -> Smash (Smash A B) C
reassocRL (smash (smash a b) c) = smash (smash a b) c
reassocRL _ = nada

-- distributivity over wedge

distributeSmash : Smash (Wedge A B) C -> Wedge (Smash A C) (Smash B C)
distributeSmash nada = nowhere
distributeSmash (smash nowhere c) = nowhere
distributeSmash (smash (here a) c) = here (smash a c)
distributeSmash (smash (there b) c) = there (smash b c)

undistributeSmash : Wedge (Smash A C) (Smash B C) -> Smash (Wedge A B) C
undistributeSmash nowhere = nada
undistributeSmash (here nada) = nada
undistributeSmash (here (smash a c)) = smash (here a) c
undistributeSmash (there nada) = nada
undistributeSmash (there (smash b c)) = smash (there b) c

-- distributivity over product

pairSmash1 : Smash (A × B) C -> (Smash A C) × (Smash B C)
pairSmash1 nada = (nada , nada)
pairSmash1 (smash (a , b) c) = (smash a c , smash b c)

unpairSmash : (Smash A C)  × (Smash B C) -> Smash (A × B) C
unpairSmash (nada , nada) = nada
unpairSmash (nada , smash b c) = nada
unpairSmash (smash a c , nada) = nada
unpairSmash (smash a c1 , smash b c2) = smash (a , b) c1 -- can choose c2

pairSmash2 : Smash A (B × C) -> (Smash A B) × (Smash A C)
pairSmash2 nada = nada , nada
pairSmash2 (smash a (b , c)) = (smash a b) , (smash a c)

unpairSmash2 : ((Smash A B) × (Smash A C)) -> Smash A (B × C)
unpairSmash2 (nada , nada) = nada
unpairSmash2 (nada , smash a c) = nada -- no a for smash
unpairSmash2 (smash a b , nada) = nada -- no c for (b,c)
unpairSmash2 (smash a1 b , smash a2 c) = smash a1 (b , c) -- could be a2

-- map

bimap : (f : A -> A') (g : B -> B') -> Smash A B -> Smash A' B'
bimap f g nada = nada
bimap f g (smash a b) = smash (f a) (g b)

map : (f : A -> A') -> Smash A B -> Smash A' B
map f = bimap f id

map-left : (g : B -> B') -> Smash A B -> Smash A B'
map-left = bimap id

-- bind

bind : Smash A B -> (f : (A × B) -> Smash A' B') -> Smash A' B'
bind nada f = nada
bind (smash a b) f = f (a , b)

bipure : A -> B -> Smash A B
bipure a b = smash a b

-- ap

biap : Smash (A -> A') (B -> B') -> Smash A B -> Smash A' B'
biap nada = \ x -> nada
biap (smash f g) = bimap f g

-- conversions

-- TODO fromSmash (toSmash mab) == mab
fromSmash : Smash A B -> Maybe (A × B)
fromSmash nada = nothing
fromSmash (smash a b) = just (a , b)

-- injection

-- TODO proove fromSmash (fromProduct ab) == Just ab
fromProduct : A × B -> Smash A B
fromProduct ab = toSmash (just ab)

{-
Smash elimination rules (projections)

x: Smash A B
----------------------
smashFst (x) : Maybe A

x: Smash A B
----------------------
smashSnd (x) : Maybe B
-}

-- TODO smashFst (smashSum (Just a) (Just b)) == Just a
smashFst : Smash A B -> Maybe A
smashFst nada = nothing
smashFst (smash a b) = just a

-- TODO smashSnd (smashSum (Just a) (Just b)) == Just b
smashSnd : Smash A B -> Maybe B
smashSnd nada = nothing
smashSnd (smash a b) = just b

-- diagonal

smashDiag : Maybe A -> Smash A A
smashDiag (just a) = smash a a
smashDiag nothing = nada

smashDiag' : A -> Smash A A
smashDiag' a = smash a a

-- TODO smashCurry (smashUncurry f) = f
-- TODO smashUncurry (smashCurry f) = f
smashCurry : (Smash A B -> Maybe C) -> Maybe A -> Maybe B -> Maybe C
smashCurry f (just a) (just b) = f (smash a b)
smashCurry f _ _ = f nada -- can we use nothing

smashUncurry : (Maybe A -> Maybe B -> Maybe C) -> Smash A B -> Maybe C
smashUncurry f nada = f nothing nothing -- can we replace with nothing
smashUncurry f (smash a b) = f (just a) (just b)

Smash-Induction : {A : Set lA} {B : Set lB} (P : Smash A B -> Set lP)
  -> P nada
  -> ((a : A) -> (b : B) -> P (smash a b))
  -> (s : Smash A B) -> P s
Smash-Induction P pn ps nada = pn
Smash-Induction P pn ps (smash a b) = ps a b
