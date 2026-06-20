module Cubical.Relation.Premetric.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Premetric.Base

open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals

open PremetricStr

ℚPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
fst ℚPremetricSpace = ℚ
_≈[_]_ (snd ℚPremetricSpace) = λ x ε y → abs (x - y) < ⟨ ε ⟩₊
isPremetric (snd ℚPremetricSpace) = isPMℚ where
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
  isPMℚ .isRounded≈ x y ε <ε =
    ∣ (mean (abs(x - y)) ⟨ ε ⟩₊ , ℚ.isTrans≤< _ _ _ (0≤abs (x - y)) (<→<mean _ ⟨ ε ⟩₊ <ε))
    , ℚ.recompute< (<→mean< (abs(x - y)) ⟨ ε ⟩₊ <ε)
    , ℚ.recompute< (<→<mean (abs(x - y)) ⟨ ε ⟩₊ <ε) ∣₁
