{-# OPTIONS --without-K --safe #-}

module Data.Wedge.Instances where

open import Data.Wedge using (Wedge)
open import Data.Wedge.Properties using (≡-dec)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; isDecEquivalence)
open import Relation.Binary.TypeClasses using (IsDecEquivalence) renaming (_≟_ to _=?_)

private
  variable
    lA lB : Level
    A  : Set lA
    B  : Set lB

instance
  Wedge-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}}
    -> {{IsDecEquivalence {A = B} _≡_}}
    -> IsDecEquivalence {A = Wedge A B} _≡_
  Wedge-≡-isDecEquivalence = isDecEquivalence (≡-dec _=?_ _=?_)
