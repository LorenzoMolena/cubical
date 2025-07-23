{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Instances.Fast.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Int.Base using (ℤ ; pos) renaming (-_ to -ℤ_)
open import Cubical.Data.Int.Fast.Base renaming (_+_ to _+ℤ_; _·_ to _·ℤ_)

open import Cubical.Data.Int.Fast.Properties as Int

open CommRingStr using (0r ; 1r ; _+_ ; _·_ ; -_ ; isCommRing)

ℤCommRing : CommRing ℓ-zero
fst ℤCommRing = ℤ
0r (snd ℤCommRing) = pos 0
1r (snd ℤCommRing) = pos 1
_+_ (snd ℤCommRing) = _+ℤ_
_·_ (snd ℤCommRing) = _·ℤ_
- snd ℤCommRing = -ℤ_
isCommRing (snd ℤCommRing) = isCommRingℤ
  where
  abstract
    isCommRingℤ : IsCommRing (pos 0) (pos 1) _+ℤ_ _·ℤ_ -ℤ_
    isCommRingℤ = makeIsCommRing isSetℤ Int.+Assoc (+IdR)
                                 -Cancel Int.+Comm Int.·Assoc
                                 Int.·IdR ·DistR+ Int.·Comm
