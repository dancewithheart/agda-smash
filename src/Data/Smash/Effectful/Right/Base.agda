{-# OPTIONS --without-K --safe #-}

open import Level

module Data.Smash.Effectful.Right.Base (la : Level) {lb} (B : Set lb) where

open import Data.Smash
open import Effect.Functor

RightSmash : Set (la ⊔ lb) -> Set (la ⊔ lb)
RightSmash A = Smash A B

functor : RawFunctor RightSmash
functor = record {
  _<$>_ = map
  }

-- TODO applicative and monad modules
-- https://github.com/agda/agda-stdlib/blob/master/src/Data/These/Effectful/Right/Base.agda
