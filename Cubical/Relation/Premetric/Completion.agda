open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion {ℓ} {ℓ'}
  (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Relation.Premetric.Completion.Base M' public
open import Cubical.Relation.Premetric.Completion.Elim M' public
