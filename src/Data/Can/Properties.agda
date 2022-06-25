{-# OPTIONS --without-K --safe #-}

module Data.Can.Properties where

open import Data.Can
open import Data.Product using (_×_; _,_; <_,_>; uncurry)
open import Function.Base using (id) renaming (_∘_ to _compose_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
  renaming (cong₂ to cong2)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality renaming (_≗_ to _==_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable renaming (map′ to dec-map)
open import Relation.Nullary.Product renaming (_×-dec_ to _*-dec_)

private
  variable
    lA lB lP lA' lB' : Level
    A  : Set lA
    B  : Set lB
    A' : Set lA'
    B' : Set lB'

-- if f1 = f2 and g1 = g2 then bimap f1 g1 = bimap f2 g2
bimap-cong : forall {f1 f2 : A -> A'} {g1 g2 : B -> B'}
  -> f1 == f2
  -> g1 == g2
  -> (bimap f1 g1) == (bimap f2 g2)
bimap-cong f1=f2 g1=g2 non = refl
bimap-cong f1=f2 g1=g2 (one a) = cong one (f1=f2 a)
bimap-cong f1=f2 g1=g2 (eno b) = cong eno (g1=g2 b)
bimap-cong f1=f2 g1=g2 (two a b) = cong₂ two (f1=f2 a) (g1=g2 b)

-- swap . swap == id
swap-involutive : (swap {A = A} {B = B} compose swap) == id
swap-involutive non = refl
swap-involutive (one a) = refl
swap-involutive (eno b) = refl
swap-involutive (two a b) = refl

-- Equality

module _ {la lb} {A : Set la} {B : Set lb} where

  one-injective : forall {a a' : A}
    -> one {B = B} a ≡ one a'
    -> a ≡ a'
  one-injective refl = refl

  eno-injective : forall {b b' : B}
    -> eno {A = A} b ≡ eno b'
    -> b ≡ b'
  eno-injective refl = refl

  two-injective-left : forall {a a' : A} {b b' : B}
    -> two a b ≡ two a' b'
    -> a ≡ a'
  two-injective-left refl = refl

  two-injective-right : forall {a a' : A} {b b' : B}
    -> two a b ≡ two a' b'
    -> b ≡ b'
  two-injective-right refl = refl

  two-injective : forall {a a' : A} {b b' : B}
    -> two a b ≡ two a' b'
    -> (a ≡ a') × (b ≡ b')
  two-injective = < two-injective-left , two-injective-right >

  ≡-dec : Decidable _≡_ -> Decidable _≡_ -> Decidable {A = Can A B} _≡_
  ≡-dec deca decb non non = yes refl
  ≡-dec deca decb (one a1) (one a2) =
     dec-map (cong one) one-injective (deca a1 a2)
  ≡-dec deca decb (eno b1) (eno b2) =
     dec-map (cong eno) eno-injective (decb b1 b2)
  ≡-dec deca decb (two a1 b1) (two a2 b2) =
     dec-map ((uncurry (cong2 two)))
             two-injective
             (deca a1 a2 *-dec decb b1 b2)
  ≡-dec deca decb non (one a) = no \ ()
  ≡-dec deca decb non (eno b) = no \ ()
  ≡-dec deca decb non (two a b) = no \ ()
  ≡-dec deca decb (one a) non = no \ ()
  ≡-dec deca decb (one a) (eno b) = no \ ()
  ≡-dec deca decb (one a1) (two a2 b2) = no \ ()
  ≡-dec deca decb (eno b) non = no \ ()
  ≡-dec deca decb (eno b) (one a) = no \ ()
  ≡-dec deca decb (eno b1) (two a b2) = no \ ()
  ≡-dec deca decb (two a b) non = no \ ()
  ≡-dec deca decb (two a1 b) (one a2) = no \ ()
  ≡-dec deca decb (two a b1) (eno b2) = no \ ()
