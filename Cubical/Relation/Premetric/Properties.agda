module Cubical.Relation.Premetric.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP


open import Cubical.Data.Sigma

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_ ; _<_ to _<ℕ_)

open import Cubical.Data.Rationals.Fast as ℚ hiding (_+_)
open import Cubical.Data.Rationals.Fast.Order as ℚ hiding (_<_ ; _≤_)

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open Positive ℚOrderedCommRing renaming (
  R₊ to ℚ₊ ; R₊AdditiveSemigroup to +ℚ₊Semigroup ; _⊔₊_ to max₊)

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Nat
open module NPL = JoinProperties ℕ≤Pseudolattice

open import Cubical.Relation.Premetric.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

module PremetricTheory (M' : PremetricSpace ℓ ℓ') where
  M = fst M'
  open PremetricStr (snd M')

  isCauchy : (ℚ₊ → M) → Type ℓ'
  isCauchy x = ∀ (ε δ : ℚ₊) → x ε ≈[ ε +₊ δ ] x δ

  isCauchySeq : (ℕ → M) → Type ℓ'
  isCauchySeq x = Σ[ N ∈ (ℚ₊ → ℕ) ] (∀ ε m n → N ε ≤ℕ m → N ε ≤ℕ n → x m ≈[ ε ] x n)

  isCauchySeq→isCauchy : ∀ x → isCauchySeq x → Σ[ y ∈ (ℚ₊ → M) ] isCauchy y
  isCauchySeq→isCauchy x (N , N≤→≈) .fst ε   = x (N ε)
  isCauchySeq→isCauchy x (N , N≤→≈) .snd ε δ = isTriangular≈
    {x (N ε)} {x (ℕ.max (N ε) (N δ))} {x (N δ)} ε δ
    (N≤→≈ ε (N ε) (ℕ.max (N ε) (N δ)) (is-refl (N ε)) NPL.L≤∨)
    (N≤→≈ δ (ℕ.max (N ε) (N δ)) (N δ) (NPL.R≤∨ {N ε}) (is-refl (N δ)))
    where open PseudolatticeStr (ℕ≤Pseudolattice .snd)
