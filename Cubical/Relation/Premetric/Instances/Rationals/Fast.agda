module Cubical.Relation.Premetric.Instances.Rationals.Fast where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation

import Cubical.Data.NatPlusOne
import Cubical.Data.Int.Fast

open import Cubical.Data.Rationals.Fast.Base as ℚ
import Cubical.Data.Rationals.Fast.Order as ℚ

open import Cubical.Algebra.Ring

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open import Cubical.Relation.Nullary


open import Cubical.Relation.Premetric.Base

open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning (ℚOrderedCommRing)
open RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ
open ℚ₊Inverse

open PremetricStr

ℚPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
fst ℚPremetricSpace = ℚ
_≈[_]_ (snd ℚPremetricSpace) = λ x ε y → abs (x - y) < ⟨ ε ⟩₊
isPremetric (snd ℚPremetricSpace) = isPMℚ
  where
    open IsPremetric

    isPMℚ : IsPremetric _
    isPMℚ .isSetM = isSetℚ
    isPMℚ .isProp≈ x y ε = is-prop-valued< (abs (x - y)) ⟨ ε ⟩₊
    isPMℚ .isRefl≈ x ε = ℚ.recompute< $ subst ((_< ⟨ ε ⟩₊) ∘ abs) (sym (+InvR x)) (ε .snd)
    isPMℚ .isSym≈ x y ε = ℚ.recompute< ∘ (subst (_< ⟨ ε ⟩₊) $ abs-Comm x y)
    isPMℚ .isSeparated≈ = selfSeparated
    isPMℚ .isTriangular≈ x y z ε δ <ε <δ = ℚ.recompute< $ begin<
      abs (x - z)                 ≤⟨ triangularInequality- x z y ⟩
      abs (x - y) + abs (y - z)   <⟨ +Mono< (abs (x - y)) ⟨ ε ⟩₊ _ _ <ε <δ ⟩
      ⟨ ε +₊ δ ⟩₊                  ◾
    isPMℚ .isRounded≈ x y ε <ε = ∣_∣₁ $
      let
        δ : ℚ₊
        δ = mean (abs(x - y)) ⟨ ε ⟩₊ , (begin<
          0                        ≤⟨ 0≤abs (x - y) ⟩
          abs(x - y)               <⟨ <→<mean (abs(x - y)) ⟨ ε ⟩₊ <ε ⟩
          mean (abs(x - y)) ⟨ ε ⟩₊ ◾)

        δ<ε : ⟨ δ ⟩₊ < ⟨ ε ⟩₊
        δ<ε = ℚ.recompute< $ <→mean< (abs(x - y)) ⟨ ε ⟩₊ <ε

        ∣x-y∣<δ : abs(x - y) < ⟨ δ ⟩₊
        ∣x-y∣<δ = ℚ.recompute< $ <→<mean (abs(x - y)) ⟨ ε ⟩₊ <ε
      in
        δ , δ<ε , ∣x-y∣<δ
