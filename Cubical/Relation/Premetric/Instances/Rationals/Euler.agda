module Cubical.Relation.Premetric.Instances.Rationals.Euler where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Empty as ⊥

open import Cubical.Data.FinData
open import Cubical.Data.Nat as ℕ renaming (
  _+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order as ℕ renaming (
  _≤_ to _≤ℕ_ ; _<_ to _<ℕ_)
open import Cubical.Data.NatPlusOne as ℕ₊₁ -- using (1+_)
open import Cubical.Data.Int.Fast   using ()

open import Cubical.Data.Rationals.Fast.Base
open import Cubical.Data.Rationals.Fast.Properties as ℚ using (max ; min ; maxComm)
open import Cubical.Data.Rationals.Fast.Order renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)


open import Cubical.Algebra.Semiring
open import Cubical.Algebra.Semiring.BigOps
open import Cubical.Algebra.Ring

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals.Fast

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Poset.Instances.Nat
open import Cubical.Relation.Binary.Order.Poset.Instances.Rationals.Fast


open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.Quoset.Instances.Nat
open import Cubical.Relation.Binary.Order.Quoset.Instances.Rationals.Fast

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Rationals.Fast

open import Cubical.Relation.Binary.Order.QuosetReasoning

open module Q = <-≤-Reasoning ℚ (ℚ≤Poset .snd) (ℚ<Quoset .snd)
  (λ x {y z} → isTrans<≤ x y z)
  (λ x {y z} → isTrans≤< x y z)
  (λ   {x y} → <Weaken≤  x y)

open module N = <-≤-Reasoning ℕ (ℕ≤Poset .snd) (ℕ<Quoset .snd)
  (λ x {y z} → ℕ.<≤-trans)
  (λ x {y z} → ℕ.≤<-trans)
  (λ   {y z} → ℕ.<-weaken)
{-
open module Q< = Q.<-syntax
open module Q≤ = Q.≤-syntax
open Q.≡-syntax
-}
open Positive ℚOrderedCommRing renaming (R₊ to ℚ₊ ; R₊AdditiveSemigroup to +ℚ₊Semigroup)

open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory (ℚOrderedCommRing)
open RingTheory (CommRing→Ring ℚCommRing)
open Sum (Ring→Semiring (CommRing→Ring ℚCommRing))


open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Instances.Rationals.Fast
open PremetricStr

open PremetricTheory ℚPremetricSpace

∑-syntax : ℕ → (ℕ → ℚ) → ℚ
∑-syntax n x = ∑ {n} λ k → x (toℕ k)

syntax ∑-syntax n (λ k → xₖ) = ∑[0 < k < n ] xₖ

-- lemmas about !
private
  _!₊₁ : ℕ → ℕ₊₁
  _!₊₁ n = 1+ predℕ (n !)

  _!>0 : ∀ n → 0 <ℕ n !
  zero !>0 = 0 , refl
  suc n !>0 = subst (0 <ℕ_) (·-comm _ (suc n)) $ <-·sk (n !>0)

  _!≠0 : ∀ n → ¬ (n ! ≡ 0)
  _!≠0 n = (<→≢ (n !>0)) ∘ sym

  !≡!₊₁ : ∀ n → ℕ₊₁→ℕ (n !₊₁) ≡ n !
  !≡!₊₁ n = sym $ suc-predℕ (n !) (n !≠0)

Seqℯ : ℕ → ℚ
Seqℯ n = ∑[0 < k < n ] [ 1 / n !₊₁ ]

{- TO DO: Prove that the sequence is cauchy
isCauchySeqℯ : isCauchySeq Seqℯ
isCauchySeqℯ .fst ε = {!   !}
isCauchySeqℯ .snd ε m n = {!   !}


Approxℯ : ℚ₊ → ℚ
Approxℯ = fst (isCauchySeq→isCauchy Seqℯ isCauchySeqℯ)

isCauchyℯ : isCauchy Approxℯ
isCauchyℯ = snd (isCauchySeq→isCauchy Seqℯ isCauchySeqℯ)
-- -}
