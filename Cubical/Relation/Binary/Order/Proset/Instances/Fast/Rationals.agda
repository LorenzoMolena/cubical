module Cubical.Relation.Binary.Order.Proset.Instances.Fast.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Proset

open import Cubical.Relation.Binary.Order.Poset.Instances.Fast.Rationals

ℚ≤Proset : Proset ℓ-zero ℓ-zero
ℚ≤Proset = Poset→Proset ℚ≤Poset
