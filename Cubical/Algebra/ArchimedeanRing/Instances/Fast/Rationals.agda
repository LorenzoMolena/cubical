module Cubical.Algebra.ArchimedeanRing.Instances.Fast.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.NatPlusOne as ℕ₊₁ using (1+_)
open import Cubical.Data.Nat as ℕ using (zero ; suc)
open import Cubical.Data.Int.Fast as ℤ using (pos ; negsuc)
open import Cubical.Data.Int.Fast.Order as ℤ using ()
open import Cubical.Data.Rationals.Fast as ℚ renaming (
  _+_ to _+ℚ_ ; _·_ to _·ℚ_ ; -_ to -ℚ_ ; _-_ to _-ℚ_ )
open import Cubical.Data.Rationals.Fast.Order as ℚ renaming (
  _<_ to _<ℚ_ ; _≤_ to _≤ℚ_ )

open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.ArchimedeanRing.Base
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Int.Fast
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast


open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open ArchimedeanRingStr
{-
ℚArchimedeanRing : ArchimedeanRing ℓ-zero ℓ-zero
fst ℚArchimedeanRing = ℚ
0r  (snd ℚArchimedeanRing) = 0
1r  (snd ℚArchimedeanRing) = 1
_+_ (snd ℚArchimedeanRing) = _+ℚ_
_·_ (snd ℚArchimedeanRing) = _·ℚ_
-_  (snd ℚArchimedeanRing) = -ℚ_
_<_ (snd ℚArchimedeanRing) = _<ℚ_
_≤_ (snd ℚArchimedeanRing) = _≤ℚ_
ι (snd ℚArchimedeanRing)   = [_/ 1 ]
isArchimedeanRing (snd ℚArchimedeanRing)  = isAR
  where
    open IsArchimedeanRing

    isAR : IsArchimedeanRing _ _ _ _ _ _ _ _
    isAR .isOrderedCommRing = OrderedCommRingStr.isOrderedCommRing (snd ℚOrderedCommRing)
    isAR .·CancelR<         = ℚ.<-·o-cancel
    isAR .isMonomorphism    = makeIsOrderedCommRingMono
      refl
      (λ x y → sym $ cong₂ (λ p q → [ p ℤ.+ q / 1 ]) (ℤ.·IdR x) (ℤ.·IdR y))
      (λ x y → refl)
      (λ x y → subst2 ℤ._≤_ (sym (ℤ.·IdR x)) (sym (ℤ.·IdR y)))
      (λ x y → subst2 ℤ._<_ (sym (ℤ.·IdR x)) (sym (ℤ.·IdR y)))
      (λ x y → subst2 ℤ._<_ (ℤ.·IdR x) (ℤ.·IdR y))
    isAR .archimedeanProperty = SQ.elimProp2
      (λ _ _ → isPropΠ2 (λ _ _ → PT.squash₁))
      λ { (pos a       , 1+ c) (negsuc b    , 1+ d) p q → ⊥.rec (ℤ.¬pos≤negsuc q)
        ; (negsuc a    , 1+ c) (pos b       , 1+ d) p q → ⊥.rec (ℤ.¬pos≤negsuc p)
        ; (negsuc a    , 1+ c) (negsuc b    , 1+ d) p q → ⊥.rec (ℤ.¬pos≤negsuc p)
        ; (pos zero    , 1+ c) (pos b       , 1+ d) p q → ⊥.rec (ℤ.isIrrefl< p)
        ; (pos (suc a) , 1+ c) (pos zero    , 1+ d) p q → ⊥.rec (ℤ.isIrrefl< q)
        ; (pos (suc a) , 1+ c) (pos (suc b) , 1+ d) p q →
          ∣ ({!   !} , {!   !}) ∣₁ }
-- -}
