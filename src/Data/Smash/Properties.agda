{-# OPTIONS --without-K --safe #-}

module Data.Smash.Properties where

open import Data.Smash
open import Data.Product using (_×_; _,_; <_,_>; uncurry)
open import Function.Bundles renaming (_↔_ to _<->_; mk↔′ to mk<->)
open import Data.Maybe.Base using (Maybe; just; nothing)
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
    lA lB lP lA' lB' lC lC' : Level
    A  : Set lA
    B  : Set lB
    A' : Set lA'
    B' : Set lB'
    C  : Set lC
    C' : Set lC'

-- if f1 = f2 and g1 = g2 then bimap f1 g1 = bimap f2 g2
bimap-cong : forall {f1 f2 : A -> A'} {g1 g2 : B -> B'}
  -> f1 == f2
  -> g1 == g2
  -> (bimap f1 g1) == (bimap f2 g2)
bimap-cong f1=f2 g1=g2 nada = refl
bimap-cong f1=g2 g1=g2 (smash a b) = cong2 smash (f1=g2 a) (g1=g2 b)

-- swap . swap == id
swap-involutive : (swap {A = A} {B = B} compose swap) == id
swap-involutive nada = refl
swap-involutive (smash b a) = refl

-- TODO smashCurry (smashUncurry f) = f
-- TODO smashUncurry (smashCurry f) = f
-- TODO fromSmash (toSmash mab) == mab
-- TODO proove fromSmash (fromProduct ab) == Just ab
-- TODO smashFst (smashSum (Just a) (Just b)) == Just a
-- TODO smashSnd (smashSum (Just a) (Just b)) == Just b

-- Equality

module _ {la lb} {A : Set la} {B : Set lb} where

  smash-injective-left : forall {a a' : A} {b b' : B}
    -> smash a b ≡ smash a' b'
    -> a ≡ a'
  smash-injective-left refl = refl

  smash-injective-right : forall {a a' : A} {b b' : B}
    -> smash a b ≡ smash a' b'
    -> b ≡ b'
  smash-injective-right refl = refl

  smash-injective : forall {a a' : A} {b b' : B}
    -> smash a b ≡ smash a' b'
    -> (a ≡ a') × (b ≡ b')
  smash-injective = < smash-injective-left , smash-injective-right >

  ≡-dec : Decidable _≡_ -> Decidable _≡_ -> Decidable {A = Smash A B} _≡_
  ≡-dec deca decb nada nada = yes refl
  ≡-dec deca decb nada (smash a b) = no \()
  ≡-dec deca decb (smash a b) nada = no \ ()
  ≡-dec deca decb (smash a1 b1) (smash a2 b2) =
     dec-map ((uncurry (cong2 smash)))
             smash-injective (deca a1 a2 *-dec decb b1 b2)
