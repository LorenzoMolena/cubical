module Cubical.Relation.Binary.Order.Quoset.Instances.Fast.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Fast.Rationals

ℚ<Quoset : Quoset ℓ-zero ℓ-zero
ℚ<Quoset = StrictOrder→Quoset ℚ<StrictOrder
