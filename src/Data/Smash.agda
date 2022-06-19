{-# OPTIONS --without-K --safe #-}

module Data.Smash where

open import Level

private
  variable
    lA lB lP : Level
    A : Set lA
    B : Set lB

data Smash {lA lB} (A : Set lA) (B : Set lB) : Set (lA ⊔ lB) where
  nada  :           Smash A B
  smash : A -> B -> Smash A B
