{-# OPTIONS --without-K --safe #-}

module Data.Can where

open import Level
open import Data.Product using (_×_; _,_)

private
  variable
    lA lB lP : Level
    A : Set lA
    B : Set lB

data Can (A : Set lA)(B : Set lB) : Set (lA ⊔ lB) where
  non : Can A B
  one : (a : A)            -> Can A B
  eno : (b : B)            -> Can A B
  two : (a : A) -> (b : B) -> Can A B
