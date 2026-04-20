module Cubical.Relation.Binary.Order.Toset.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order renaming (_≤_ to _≤ℚ_)

open import Cubical.Relation.Binary.Order.Toset

open import Cubical.Relation.Binary
open BinaryRelation

open TosetStr

ℚ≤Toset : Toset ℓ-zero ℓ-zero
fst ℚ≤Toset = ℚ
_≤_ (snd ℚ≤Toset) = _≤ℚ_
isToset (snd ℚ≤Toset) = isTosetℚ≤
  where
    open IsToset
    abstract
      isTosetℚ≤ : IsToset _≤ℚ_
      isTosetℚ≤ .is-set         = isSetℚ
      isTosetℚ≤ .is-prop-valued = isProp≤
      isTosetℚ≤ .is-refl        = isRefl≤
      isTosetℚ≤ .is-trans       = isTrans≤
      isTosetℚ≤ .is-antisym     = isAntisym≤
      isTosetℚ≤ .is-total       = isTotal≤
