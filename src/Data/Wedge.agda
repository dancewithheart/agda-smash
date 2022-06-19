{-# OPTIONS --without-K --safe #-}

module Data.Wedge where

open import Level
open import Data.Product using (_×_; _,_)

private
  variable
    lA lB lP : Level
    A : Set lA
    B : Set lB
    P : Set lP

data Wedge {lA lB} (A : Set lA)(B : Set lB) : Set (lA ⊔ lB) where
  nowhere : Wedge A B
  here : (a : A) -> Wedge A B
  there : (b : B) -> Wedge A B
