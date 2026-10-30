module Cubical.Algebra.ValuedField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP

open import Cubical.Algebra.ArchimedeanField.Base
open import Cubical.Algebra.HeytingField.Base

open import Cubical.Data.Sum as ⊎

private
  variable
    ℓ ℓ' ℓ# ℓ<≤ ℓ<≤' : Level

record IsValuation {F : Type ℓ} {R : Type ℓ'}
  (Fstr : HeytingFieldStr ℓ# F)
  (∣_∣ : F → R)
  (Rstr : ArchimedeanFieldStr ℓ<≤ R)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ# ℓ<≤)))
  where
  no-eta-equality
  constructor isvaluation

  open HeytingFieldStr     Fstr
  open ArchimedeanFieldStr Rstr
    renaming (0f to 0r ; _+_ to _+r_ ; _·_ to _·r_) hiding (-_)

  field
    isNonNegative∣    : ∀ x   → 0r ≤ ∣ x ∣
    isSymmetric∣      : ∀ x   → ∣ - x ∣ ≡ ∣ x ∣ -- this is actualy redundant
    isTriangular∣     : ∀ x y → ∣ x + y ∣ ≤ ∣ x ∣ +r ∣ y ∣
    isMultiplicative∣ : ∀ x y → ∣ x · y ∣ ≡ ∣ x ∣ ·r ∣ y ∣
    isApartFrom0∣     : ∀ x   → (x # 0f) ≃ ((∣ x ∣ < 0r) ⊎ (0r < ∣ x ∣))

record IsValuedField (R : ArchimedeanField ℓ' ℓ<≤) {F : Type ℓ}
  (0f 1f : F)
  (_+_ _·_ : F → F → F)
  (-_ : F → F)
  (_#_ : F → F → Type ℓ#)
  (∣_∣ : F → ⟨ R ⟩)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ# ℓ<≤))) where
  no-eta-equality
  constructor isvaluedfield
  field
    isHeytingField : IsHeytingField 0f 1f _+_ _·_ -_ _#_
    isValuation∣   : IsValuation (heytingfieldstr _ _ _ _ _ _ isHeytingField) ∣_∣ (snd R)

  open IsHeytingField isHeytingField public
  open IsValuation isValuation∣ public

record ValuedFieldStr (R : ArchimedeanField ℓ' ℓ<≤) (ℓ# : Level) (F : Type ℓ)
  : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ# ℓ<≤)))) where
  constructor valuedfieldstr
  field
    0f 1f : F
    _+_ _·_ : F → F → F
    -_ : F → F
    _#_ : F → F → Type ℓ#
    ∣_∣ : F → ⟨ R ⟩
    isValuedField : IsValuedField R 0f 1f _+_ _·_ -_ _#_ ∣_∣

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix  4 _#_

  open IsValuedField isValuedField public

ValuedField : (ArchimedeanField ℓ' ℓ<≤) → (ℓ ℓ# : Level)
            → Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ# ℓ<≤))))
ValuedField R ℓ ℓ# = TypeWithStr ℓ (ValuedFieldStr R ℓ#)

module _ {R : ArchimedeanField ℓ' ℓ<≤} where
  ValuedField→HeytingField : ValuedField R ℓ ℓ# → HeytingField ℓ ℓ#
  fst (ValuedField→HeytingField F) = fst F
  snd (ValuedField→HeytingField F) = heytingfieldstr _ _ _ _ _ _ isHeytingField
    where open ValuedFieldStr (snd F)
