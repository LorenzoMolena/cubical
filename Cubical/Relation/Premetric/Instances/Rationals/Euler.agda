module Cubical.Relation.Premetric.Instances.Rationals.Euler where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Cubical.Data.FinData
open import Cubical.Data.Nat as ℕ renaming (
  _+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order as ℕ renaming (
  _≤_ to _≤ℕ_ ; _<_ to _<ℕ_)
open import Cubical.Data.Nat.Mod using (quotient'_/_ ; remainder'_/_)
open import Cubical.Data.NatPlusOne as ℕ₊₁ -- using (1+_)
open import Cubical.Data.Int.Fast as ℤ renaming (
  _+_ to _+ℤ_ ; _·_ to _·ℤ_ ; _-_ to _-ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Int.Fast.Order as ℤ renaming (_≤_ to _≤ℤ_ ; _<_ to _<ℤ_)

open import Cubical.Data.Rationals.Fast.Base
open import Cubical.Data.Rationals.Fast.Properties as ℚ using (reduce ; reduced)
open import Cubical.Data.Rationals.Fast.Order renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)


open import Cubical.Algebra.Semiring
open import Cubical.Algebra.Semiring.BigOps
open import Cubical.Algebra.Ring

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals.Fast

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Int.Fast
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Poset.Instances.Nat
open import Cubical.Relation.Binary.Order.Poset.Instances.Int.Fast
open import Cubical.Relation.Binary.Order.Poset.Instances.Rationals.Fast


open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.Quoset.Instances.Nat
open import Cubical.Relation.Binary.Order.Quoset.Instances.Int.Fast
open import Cubical.Relation.Binary.Order.Quoset.Instances.Rationals.Fast

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Rationals.Fast

open import Cubical.Relation.Binary.Order.QuosetReasoning

open module Z = <-≤-Reasoning ℤ (ℤ≤Poset .snd) (ℤ<Quoset .snd)
  (λ x {y z} → ℤ.<≤-trans {x})
  (λ x {y z} → ℤ.≤<-trans {x})
  (λ   {x y} → ℤ.<-weaken {x})

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

∑ʳ-syntax : ℕ → (ℕ → ℚ) → ℚ
∑ʳ-syntax zero x = 0
∑ʳ-syntax (suc n) x = reduce (x 0) + reduce (∑ʳ-syntax n (x ∘ suc))

syntax ∑ʳ-syntax n (λ k → xₖ) = ∑ʳ[0 < k < n ] xₖ

∑ʳ≡∑ : ∀ n → (x : ℕ → ℚ) → (∑ʳ[0 < k < n ] (x k) ≡ ∑[0 < k < n ] (x k))
∑ʳ≡∑ zero    x = refl
∑ʳ≡∑ (suc n) x = cong₂ _+_ (ℚ.reduce≡id (x 0)) (ℚ.reduce≡id _ ∙ ∑ʳ≡∑ n (x ∘ suc))

-- lemmas about !
private
  _!₊₁ : ℕ → ℕ₊₁
  _!₊₁ n = 1+ predℕ (n !)

  _!>0 : ∀ n → 0 <ℕ n !
  zero !>0 = 0 , refl
  suc n !>0 = subst (0 <ℕ_) (·-comm _ (suc n)) $ <-·sk (n !>0)

  !Bound : ∀ n k → (suc n !) ·ℕ (suc n) ^ k ≤ℕ (n +ℕ suc k)!
  !Bound n zero = ℕ.≤-reflexive $
    (suc n !) ·ℕ 1 ≡⟨ ·-identityʳ _ ⟩
     suc n !       ≡⟨ cong _! (+-comm 1 n) ⟩
    (n +ℕ 1)!      ∎
  !Bound n (suc k) = N.begin≤
    (suc n !) ·ℕ (suc n ·ℕ (suc n) ^ k) ≡→≤⟨ ℕ.·-assoc (suc n !) _ _ ⟩
    ((suc n !) ·ℕ suc n) ·ℕ (suc n) ^ k ≡→≤⟨ cong (_·ℕ suc n ^ k) $ ℕ.·-comm (suc n !) _ ⟩
    (suc n ·ℕ (suc n !)) ·ℕ (suc n) ^ k ≡→≤⟨ sym $ ℕ.·-assoc (suc n) (suc n !) _ ⟩
    suc n ·ℕ ((suc n !) ·ℕ (suc n) ^ k) ≡→≤⟨ ·-comm (suc n) _ ⟩
    ((suc n !) ·ℕ (suc n) ^ k) ·ℕ suc n   ≤⟨ ℕ.≤-·k (!Bound n k) ⟩
    ((n +ℕ suc k)!) ·ℕ suc n            ≡→≤⟨ ·-comm _ (suc n) ⟩
    suc n ·ℕ ((n +ℕ suc k)!)              ≤⟨ ℕ.≤-·k (suc k , ℕ.+-comm _ (suc n)) ⟩
    (suc n +ℕ suc k) ·ℕ ((n +ℕ suc k)!) ≡→≤⟨ sym $ cong _! (ℕ.+-suc n (suc k)) ⟩
    (n +ℕ suc (suc k)) !                N.◾
    where open N.≤-syntax ; open N.≡-syntax

  _!≠0 : ∀ n → ¬ (n ! ≡ 0)
  _!≠0 n = (<→≢ (n !>0)) ∘ sym

  !≡!₊₁ : ∀ n → ℕ₊₁→ℕ (n !₊₁) ≡ n !
  !≡!₊₁ n = sym $ suc-predℕ (n !) (n !≠0)

Seqℯ : ℕ → ℚ
Seqℯ n = ∑[0 < k < n ] [ 1 / k !₊₁ ]

Seqʳℯ : ℕ → ℚ
Seqʳℯ n = ∑ʳ[0 < k < n ] [ 1 / k !₊₁ ]

SeqℯFrac : ℕ → ℤ × ℕ₊₁
SeqℯFrac = fst ∘ reduced ∘ Seqℯ

ℯDigits : (iterations : ℕ) → (digits : ℕ) → ℕ × ℕ
ℯDigits n d =
  let
    frac = SeqℯFrac n ; num = ℤ.abs (fst frac) ; den = ℕ₊₁→ℕ (snd frac)
    integerPart    = quotient' num / den
    fractionalPart = quotient' (10 ^ d) ·ℕ (num ℕ.∸ (den ·ℕ integerPart)) / den
  in
    integerPart , fractionalPart

Seqʳℯ≡Seqℯ : ∀ n → Seqʳℯ n ≡ Seqℯ n
Seqʳℯ≡Seqℯ n = ∑ʳ≡∑ n _

-- WIP
-- first 50 digits:
-- 2.71828182845904523536028747135266249775724709369995
-- for ℯDigits 50 50, this produces the same output
-- and its computed instantly

-- I'm working on the proof of Cauchy, so we will be able to pass the error
-- ε = 10⁻ᵈ , and it will produce a number N together with a proof that
-- Seqℯ N is less than ε from its limit

{-
ℚUpperBoundℕ : ∀ x → Σ[ N ∈ ℕ ] x <ℚ [ pos N / 1 ]
ℚUpperBoundℕ x =
  let
    (num , den) = fst (reduced x)
    N = suc (ℤ.abs num)
  in
    N , (subst (_<ℚ [ pos N / 1 ]) (ℚ.reduce≡id x) $ Z.begin<
      {! num · 1 ≤⟨ ? ⟩ ? !})
  where
    open Z.≡-syntax ; open Z.≤-syntax ; open Z.<-syntax
    open OrderedCommRingTheory ℤOrderedCommRing
-}
{- TO DO: Prove that the sequence is cauchy

proof sketch:

  • normalize ε to a/b

  • notice that
    (n + 1)! (n + 1)ᵏ ≤ (n + 1 + k)! (∗)

  • set N(ε) := ⌈b/a⌉ + 1
    then
      b/a ≤ ⌈b/a⌉ < ⌈b/a⌉ + 1 = N ≤ N · N! and
      (**) 1/(N · N!) ≤ a/b = ε

  • by trichotomy it suffices* to consider N ≤ n < m := n + 1 + r
    (*formally: • prove it for n < m, parametrically in n and m and callet h
                • for n ≡ m , then we get 0, which is smaller than ε
                • for n > n , use h m n, possibly using some commutativity at the start)

  • for N ≤ n < n + 1 + r, we finally have:

  |∑₀ⁿ⁺¹⁺ʳ 1/k! - ∑₀ⁿ 1/k!| = |∑ₙ₊₁ⁿ⁺¹⁺ʳ 1/k!|
                            = |∑₀ʳ 1/(n + 1 + k)!|
                        (∗) ≤ |∑₀ʳ 1/((n + 1)! (n + 1)ᵏ)|
                            = |1/(n + 1)! · ∑₀ʳ 1/(n + 1)ᵏ|
            (Geometric Sum) = |1/(n + 1)! · (1 - (1/(n + 1))ʳ⁺¹)/(1 - 1/(n + 1))|
                            ≤ |1/(n + 1)! · 1/(1 - 1/(n + 1))|
                            = |1/(n + 1)! · 1/(n/(n + 1))|
                            = |1/(n + 1)! · (n+1)/n|
                            = |1/(n · n!)|
                            ≤ |1/(N · N!)|
                       (**) ≤ ε


isCauchySeqℯ : isCauchySeq Seqℯ
isCauchySeqℯ .fst ε = {!   !}
isCauchySeqℯ .snd ε m n = {!   !}


Approxℯ : ℚ₊ → ℚ
Approxℯ = fst (isCauchySeq→isCauchy Seqℯ isCauchySeqℯ)

isCauchyℯ : isCauchy Approxℯ
isCauchyℯ = snd (isCauchySeq→isCauchy Seqℯ isCauchySeqℯ)
-- -}
