module Cubical.Relation.Premetric.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open Positive ℚOrderedCommRing renaming (
    R₊ to ℚ₊ ; _⊔₊_ to max₊
  ; R₊AdditiveSemigroup to +ℚ₊Semigroup
  ; R₊MultiplicativeCommMonoid to ·ℚ₊CommMonoid) public

private
  variable
    ℓ ℓ' ℓ'' : Level

record IsPremetric {M : Type ℓ}
                        (_≈[_]_ : M → ℚ₊ → M → Type ℓ') : Type (ℓ-max ℓ ℓ') where

  constructor ispremetric

  field
    isSetM        : isSet M
    isProp≈       : ∀ x y ε → isProp (x ≈[ ε ] y)
    isRefl≈       : ∀ x     ε   → x ≈[ ε ] x
    isSym≈        : ∀ x y   ε   → x ≈[ ε ] y → y ≈[ ε ] x
    isSeparated≈  : ∀ x y       → (∀ ε → x ≈[ ε ] y) → x ≡ y
    isTriangular≈ : ∀ x y z ε δ → x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε +₊ δ ] z
    isRounded≈    : ∀ x y   ε   → x ≈[ ε ] y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x ≈[ δ ] y)

unquoteDecl IsPremetricIsoΣ = declareRecordIsoΣ IsPremetricIsoΣ (quote IsPremetric)


record PremetricStr (ℓ' : Level) (M : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  constructor premetricstr

  field
    _≈[_]_      : M → ℚ₊ → M → Type ℓ'
    isPremetric : IsPremetric _≈[_]_

  open IsPremetric isPremetric public

PremetricSpace : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
PremetricSpace ℓ ℓ' = TypeWithStr ℓ (PremetricStr ℓ')

premetricspace : (M : Type ℓ)
                  → (_≈[_]_ : M → ℚ₊ → M → Type ℓ')
                  → IsPremetric _≈[_]_
                  → PremetricSpace ℓ ℓ'
premetricspace M (_≈[_]_) pm = M , (premetricstr _≈[_]_ pm)
