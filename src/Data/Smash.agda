{-# OPTIONS --without-K --safe #-}

module Data.Smash where

open import Level
open import Data.Product using (_×_; _,_)

private
  variable
    lA lB lP : Level
    A : Set lA
    B : Set lB

data Smash {lA lB} (A : Set lA) (B : Set lB) : Set (lA ⊔ lB) where
  nada  :           Smash A B
  smash : A -> B -> Smash A B

fromProduct : A × B -> Smash A B
fromProduct (a , b) = smash a b

swap : Smash A B -> Smash B A
swap nada = nada
swap (smash a b) = smash b a
