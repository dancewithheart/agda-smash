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

Smash-Induction : {A : Set lA} {B : Set lB} (P : Smash A B -> Set lP)
  -> P nada
  -> ((a : A) -> (b : B) -> P (smash a b))
  -> (s : Smash A B) -> P s
Smash-Induction P pn ps nada = pn
Smash-Induction P pn ps (smash a b) = ps a b
