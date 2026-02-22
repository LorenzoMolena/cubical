module Cubical.Relation.Binary.Order.Pseudolattice.Instances.Fast.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Fast.Rationals
open import Cubical.Data.Fast.Rationals.Order renaming (_≤_ to _≤ℚ_)

open import Cubical.Relation.Binary.Order.Poset.Instances.Fast.Rationals
open import Cubical.Relation.Binary.Order.Pseudolattice

ℚ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℚ≤Pseudolattice = makePseudolatticeFromPoset ℚ≤Poset min max
  (min≤ _ _)
  (λ {a b} → recompute≤ (subst (_≤ℚ _) (minComm b a) (min≤ _ _)))
  (λ {a b} x≤a x≤b → recompute≤ (subst (_≤ℚ min a b) (minIdem _) (≤MonotoneMin _ a _ b x≤a x≤b)))
  (≤max _ _)
  (λ {a b} → recompute≤ (subst (_ ≤ℚ_) (maxComm b a) (≤max _ _)))
  (λ {a b} a≤x b≤x → recompute≤ (subst (max a b ≤ℚ_) (maxIdem _) (≤MonotoneMax a _ b _ a≤x b≤x)))
