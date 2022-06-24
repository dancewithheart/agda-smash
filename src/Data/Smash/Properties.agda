{-# OPTIONS --without-K --safe #-}

module Data.Smash.Properties where

open import Data.Smash
open import Data.Product using (_×_; _,_; <_,_>; uncurry)
open import Function.Bundles renaming (_↔_ to _<->_; mk↔′ to mk<->)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
  renaming (cong₂ to cong2)
open import Relation.Binary using (Decidable)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable renaming (map′ to dec-map)
open import Relation.Nullary.Product renaming (_×-dec_ to _*-dec_)

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
