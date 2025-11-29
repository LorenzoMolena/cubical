module Cubical.Relation.Premetric.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP


open import Cubical.Data.Sigma

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ renaming (_≤_ to _≤ℕ_ ; _<_ to _<ℕ_)

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Nat
open module N = JoinProperties ℕ≤Pseudolattice

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

  isCauchySeq< : (ℕ → M) → Type ℓ'
  isCauchySeq< x = Σ[ N ∈ (ℚ₊ → ℕ) ] (∀ ε m n → m <ℕ n → N ε ≤ℕ m → x m ≈[ ε ] x n)

  isCauchySeq→isCauchy : ∀ x → isCauchySeq x → Σ[ y ∈ (ℚ₊ → M) ] isCauchy y
  isCauchySeq→isCauchy x (N , N≤→≈) .fst ε   = x (N ε)
  isCauchySeq→isCauchy x (N , N≤→≈) .snd ε δ =
    isTriangular≈ _ (x (ℕ.max (N ε) (N δ))) _ ε δ
    (N≤→≈ ε (N ε) (ℕ.max (N ε) (N δ)) (ℕ.≤-refl) (N.L≤∨ {N ε}))
    (N≤→≈ δ (ℕ.max (N ε) (N δ)) (N δ) (N.R≤∨ {N ε}) (ℕ.≤-refl))

  -- this formalizes "WLOG assume m < n"
  isCauchySeq<→isCauchySeq : ∀ x → isCauchySeq< x → isCauchySeq x
  isCauchySeq<→isCauchySeq x (N , xcs<) .fst = N
  isCauchySeq<→isCauchySeq x (N , xcs<) .snd ε m n with m ℕ.≟ n
  ... | lt m<n = λ N≤m _   → xcs< ε m n m<n N≤m
  ... | eq m≡n = λ _   _   → subst ((x m ≈[ ε ]_) ∘ x) m≡n (isRefl≈ _ ε)
  ... | gt m>n = λ _   N≤n → isSym≈ _ _ ε $ xcs< ε n m m>n N≤n

  isCauchySeq<→isCauchy : ∀ x → isCauchySeq< x → Σ[ y ∈ (ℚ₊ → M) ] isCauchy y
  isCauchySeq<→isCauchy x = isCauchySeq→isCauchy x ∘ isCauchySeq<→isCauchySeq x
