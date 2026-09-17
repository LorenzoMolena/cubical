module Cubical.Algebra.OrderedField.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Rationals as ℚ
  renaming (_+_ to _+ℚ_ ; _-_ to _-ℚ_; -_ to -ℚ_ ; _·_ to _·ℚ_)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Sum

open import Cubical.Algebra.Field.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedField.Base

open OrderedFieldStr
open OrderedCommRingStr

ℚOrderedField : OrderedField ℓ-zero ℓ-zero
fst ℚOrderedField = ℚ
0f  (snd ℚOrderedField) = 0
1f  (snd ℚOrderedField) = 1
_+_ (snd ℚOrderedField) = _+ℚ_
_·_ (snd ℚOrderedField) = _·ℚ_
-_  (snd ℚOrderedField) = -ℚ_
_<_ (snd ℚOrderedField) = _<ℚ_
_≤_ (snd ℚOrderedField) = _≤ℚ_
isOrderedField (snd ℚOrderedField) = isOrderedFieldℚ
  where
  open IsOrderedField

  isInv→#0ℚ : (x y : ℚ) → x ·ℚ y ≡ 1 → (x <ℚ 0) ⊎ (0 <ℚ x)
  isInv→#0ℚ x y xy≡1 with x ℚ.≟ 0
  ... | lt x<0 = inl x<0
  ... | eq x≡0 = ⊥.rec $ 0≢1-ℚ $ sym $ sym xy≡1 ∙∙ congL _·ℚ_ x≡0 ∙∙ ℚ.·AnnihilL y
  ... | gt 0<x = inr 0<x

  isOrderedFieldℚ : IsOrderedField 0 1 _+ℚ_ _·ℚ_ -ℚ_ _<ℚ_ _≤ℚ_
  isOrderedFieldℚ .isOrderedCommRing = isOrderedCommRing $ snd ℚOrderedCommRing
  isOrderedFieldℚ .#0→isInv = λ x → hasInverseℚ x ∘ (ℚ.isIrrefl# 0 ∘_) ∘ flip subst#L
  isOrderedFieldℚ .isInv→#0 = isInv→#0ℚ
