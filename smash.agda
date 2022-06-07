{-# OPTIONS --without-K --exact-split --safe #-}

module smash where

open import Agda.Primitive public
 renaming ( Level to Universe
          ; _⊔_ to _umax_     -- Least upper bound of two universes, e.g. Universe1 ⊔ Universe0 is Universe1
          )

Type = \ u -> Set u

-- declare variables (placeholder) for Universes
variable UniverseU UniverseV UniverseW UniverseX : Universe

-- TODO Remove it as it is already done: https://github.com/agda/agda-stdlib/blob/master/src/Data/These.agda
-- TODO recursion, Pair + Either == These
data These (X : Type UniverseU)(Y : Type UniverseV) : Type (UniverseU umax UniverseV) where
  this : (x : X) -> These X Y
  that : (y : Y) -> These X Y
  these : (x : X) -> (y : Y) -> These X Y

-- TODO induction
These-induction : {X : Type UniverseU} {Y : Type UniverseV} (P : These X Y -> Type UniverseW)
  -> ((x : X) -> P (this x))
  -> ((y : Y) -> P (that y))
  -> ((x : X) -> (y : Y) -> P (these x y))
  -> (t : These X Y) -> P t
These-induction P xpx ypy xypxy (this x) = xpx x
These-induction P xpx ypy xypxy (that y) = ypy y
These-induction P xpx ypy xypxy (these x y) = xypxy x y

-- TODO recursion, 1 + Either == Wedge
data Wedge (X : Type UniverseU)(Y : Type UniverseV) : Type (UniverseU umax UniverseV) where
  nowhere : Wedge X Y
  here : (x : X) -> Wedge X Y
  there : (y : Y) -> Wedge X Y

Wedge-induction : {X : Type UniverseU} {Y : Type UniverseV} (P : Wedge X Y -> Type UniverseW)
 -> P nowhere
 -> ((x : X) -> P (here x))
 -> ((y : Y) -> P (there y))
 -> (w : Wedge X Y) -> P w
Wedge-induction P pn _ _ nowhere = pn
Wedge-induction P _ ph _ (here x) = ph x
Wedge-induction P _ _ pt (there y) = pt y

-- TODO recursion, 1 + Pair == Smash
data Smash (X : Type UniverseU) (Y : Type UniverseV) : Type (UniverseU umax UniverseV) where
  nada : Smash X Y
  smash : (x : X) -> (y : Y) -> Smash X Y

Smash-induction : {X : Type UniverseU} {Y : Type UniverseV} (P : Smash X Y -> Type UniverseW)
  -> P nada
  -> ((x : X) -> (y : Y) -> P (smash x y))
  -> (s : Smash X Y) -> P s
Smash-induction P pn ps nada = pn
Smash-induction P pn ps (smash x y) = ps x y

-- TODO recursion, 1 + These == Can
data Can (X : Type UniverseU)(Y : Type UniverseV) : Type (UniverseU umax UniverseV) where
  non : Can X Y
  one : (x : X) -> Can X Y
  eno : (y : Y) -> Can X Y
  two : (x : X) -> (y : Y) -> Can X Y
