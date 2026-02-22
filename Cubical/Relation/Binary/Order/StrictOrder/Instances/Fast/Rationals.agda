module Cubical.Relation.Binary.Order.StrictOrder.Instances.Fast.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Loset

open import Cubical.Relation.Binary.Order.Loset.Instances.Fast.Rationals

ℚ<StrictOrder : StrictOrder ℓ-zero ℓ-zero
ℚ<StrictOrder = Loset→StrictOrder ℚ<Loset
