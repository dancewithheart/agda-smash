{-# OPTIONS --without-K --safe #-}

module Data.Can.Instances where

open import Data.Can using (Can)
open import Data.Can.Properties using (≡-dec)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; isDecEquivalence)
open import Relation.Binary.TypeClasses using (IsDecEquivalence) renaming (_≟_ to _=?_)

private
  variable
    lA lB : Level
    A  : Set lA
    B  : Set lB

instance
  Can-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}}
    -> {{IsDecEquivalence {A = B} _≡_}}
    -> IsDecEquivalence {A = Can A B} _≡_
  Can-≡-isDecEquivalence = isDecEquivalence (≡-dec _=?_ _=?_)
