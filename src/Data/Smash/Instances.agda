{-# OPTIONS --without-K --safe #-}

module Data.Smash.Instances where

open import Data.Smash using (Smash)
open import Data.Smash.Properties using (≡-dec)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; isDecEquivalence)
open import Relation.Binary.TypeClasses using (IsDecEquivalence) renaming (_≟_ to _=?_)

private
  variable
    lA lB : Level
    A  : Set lA
    B  : Set lB

instance
  Smash-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}}
    -> {{IsDecEquivalence {A = B} _≡_}}
    -> IsDecEquivalence {A = Smash A B} _≡_
  Smash-≡-isDecEquivalence = isDecEquivalence (≡-dec _=?_ _=?_)
