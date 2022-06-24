{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Level

module Data.Smash.Effectful.Right(la : Level) {c l} (W : Semigroup c l) where

open Semigroup W using (Carrier) renaming (_∙_ to _*_)
open import Data.Smash.Effectful.Right.Base la Carrier public

open import Data.Smash
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)

module _ {la lb} {A : Set la} {B : Set lb} where

applicative : (b : Carrier) -> RawApplicative RightSmash
applicative b = record {
  pure = \ a -> smash a b ;
  _⊛_ = ap
  } where
     ap : forall {X Y} -> RightSmash (X -> Y) -> RightSmash X -> RightSmash Y
     ap nada _ = nada
     ap (smash a b) nada = nada
     ap (smash f cr1) (smash x cr2) = smash (f x) (cr1 * cr2)

monad : (b : Carrier) -> RawMonad RightSmash
monad b = record {
  return = \ a -> smash a b ;
  _>>=_ = bindr
  } where
     bindr : forall {A B} -> RightSmash A -> (A -> RightSmash B) -> RightSmash B
     bindr nada f = nada
     bindr (smash a b2) f = smash {! f aa  !} (b * b2) -- TODO with
