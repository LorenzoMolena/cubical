open import Cubical.Algebra.OrderedCommRing

module Cubical.Relation.Premetric.PremetricOver.Base {ℓR} {ℓR'}
  (R' : OrderedCommRing ℓR ℓR') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Algebra.OrderedCommRing

private
  R = fst R'
  variable
    ℓ ℓ' ℓ'' : Level

open OrderedCommRingStr (str R')
open Positive R'

record IsPremetricOver {M : Type ℓ}
  (_≈[_]_ : M → R₊ → M → Type ℓ') : Type (ℓ-max (ℓ-max (ℓ-max ℓR ℓR') ℓ) ℓ') where

  constructor ispremetricover

  field
    isSetM        : isSet M
    isProp≈       : ∀ x y ε → isProp (x ≈[ ε ] y)
    isRefl≈       : ∀ x     ε   → x ≈[ ε ] x
    isSym≈        : ∀ x y   ε   → x ≈[ ε ] y → y ≈[ ε ] x
    isSeparated≈  : ∀ x y       → (∀ ε → x ≈[ ε ] y) → x ≡ y
    isTriangular≈ : ∀ x y z ε δ → x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε +₊ δ ] z
    isRounded≈    : ∀ x y   ε   → x ≈[ ε ] y → ∃[ δ ∈ R₊ ] (δ <₊ ε) × (x ≈[ δ ] y)

unquoteDecl IsPremetricOverIsoΣ = declareRecordIsoΣ IsPremetricOverIsoΣ (quote IsPremetricOver)

record R-PremetricStr
  (ℓ' : Level) (M : Type ℓ) : Type (ℓ-suc (ℓ-max (ℓ-max (ℓ-max ℓR ℓR') ℓ) ℓ')) where

  constructor premetricstrover

  field
    _≈[_]_          : M → R₊ → M → Type ℓ'
    isPremetricOver : IsPremetricOver _≈[_]_

  open IsPremetricOver isPremetricOver public

R-PremetricSpace : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max (ℓ-max (ℓ-max ℓR ℓR') ℓ) ℓ'))
R-PremetricSpace ℓ ℓ' = TypeWithStr ℓ (R-PremetricStr ℓ')

premetricspaceover : (M : Type ℓ)
                  → (_≈[_]_ : M → R₊ → M → Type ℓ')
                  → IsPremetricOver _≈[_]_
                  → R-PremetricSpace ℓ ℓ'
premetricspaceover M (_≈[_]_) pm = M , (premetricstrover _≈[_]_ pm)
