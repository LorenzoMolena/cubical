{-

ℚ is a CommRing

-}
module Cubical.Algebra.CommRing.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Fast.Int
open import Cubical.Data.NatPlusOne using ()
import Cubical.Data.Fast.Int as ℤ
open import Cubical.Data.Rationals as ℚ

ℚCommRing : CommRing ℓ-zero
ℚCommRing .fst = ℚ
ℚCommRing .snd .CommRingStr.0r = 0
ℚCommRing .snd .CommRingStr.1r = 1
ℚCommRing .snd .CommRingStr._+_ = _+_
ℚCommRing .snd .CommRingStr._·_ = _·_
ℚCommRing .snd .CommRingStr.-_  = -_
ℚCommRing .snd .CommRingStr.isCommRing = p
  where
  p : IsCommRing 0 1 _+_ _·_ (-_)
  p = makeIsCommRing isSetℚ +Assoc +IdR +InvR +Comm ·Assoc ·IdR ·DistL+ ·Comm

open IsCommRingHom
ℤ→ℚCR : CommRingHom ℤCommRing ℚCommRing
fst ℤ→ℚCR = [_/ 1 ]
snd ℤ→ℚCR .pres0 = refl
snd ℤ→ℚCR .pres1 = refl
snd ℤ→ℚCR .pres· = λ x y   → refl
snd ℤ→ℚCR .pres+ = λ x y i → [ ℤ.·IdR x (~ i) ℤ.+ ℤ.·IdR y (~ i) / 1 ]
snd ℤ→ℚCR .pres- = λ x i   → [ ℤ.-1·x≡-x x (~ i) / 1 ]
