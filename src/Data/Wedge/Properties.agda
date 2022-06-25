{-# OPTIONS --without-K --safe #-}

module Data.Wedge.Properties where

open import Data.Wedge
open import Data.Product using (_×_; _,_; <_,_>; uncurry)
open import Function.Base using (id) renaming (_∘_ to _compose_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
  renaming (cong₂ to cong2)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality renaming (_≗_ to _==_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable renaming (map′ to dec-map)
open import Relation.Nullary.Product renaming (_×-dec_ to _*-dec_)

private
  variable
    lA lB lP lA' lB' : Level
    A  : Set lA
    B  : Set lB
    A' : Set lA'
    B' : Set lB'

-- if f1 = f2 and g1 = g2 and w: We then bimap f1 g1 w = bimap f2 g2 w
bimap-cong : forall {f1 f2 : A -> A'} {g1 g2 : B -> B'}
  -> f1 == f2
  -> g1 == g2
  -> (bimap f1 g1) == (bimap f2 g2)
bimap-cong f1=f2 g1=g2 nowhere = refl
bimap-cong f1=f2 g1=g2 (here a) = cong here (f1=f2 a)
bimap-cong f1=f2 g1=g2 (there b) = cong there (g1=g2 b)

-- swap . swap == id
swap-involutive : (swap {A = A} {B = B} compose swap) == id
swap-involutive nowhere = refl
swap-involutive (here x) = refl
swap-involutive (there x) = refl

-- Equality

module _ {la lb} {A : Set la} {B : Set lb} where

  here-injective : forall {a a' : A}
    -> here {B = B} a ≡ here a'
    -> a ≡ a'
  here-injective refl = refl

  there-injective : forall {b b' : B}
    -> there {A = A} b ≡ there b'
    -> b ≡ b'
  there-injective refl = refl

  ≡-dec : Decidable _≡_ -> Decidable _≡_ -> Decidable {A = Wedge A B} _≡_
  ≡-dec decA decB nowhere nowhere = yes refl
  ≡-dec decA decB (here a1) (here a2) =
    dec-map (cong here) here-injective (decA a1 a2)
  ≡-dec decA decB (there b1) (there b2) =
    dec-map (cong there) there-injective (decB b1 b2)
  ≡-dec decA decB nowhere (here x) = no \ ()
  ≡-dec decA decB nowhere (there x) = no \ ()
  ≡-dec decA decB (here a) nowhere = no \ ()
  ≡-dec decA decB (here a) (there b) = no \ ()
  ≡-dec decA decB (there b) nowhere = no \ ()
  ≡-dec decA decB (there b) (here a) = no \ ()
