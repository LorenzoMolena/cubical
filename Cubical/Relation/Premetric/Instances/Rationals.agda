module Cubical.Relation.Premetric.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Mappings

open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing
open RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)
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

-ⁿ : NE[ ℚPremetricSpace , ℚPremetricSpace ]
(fst -ⁿ) = -_
IsNonExpansive.pres≈ (snd -ⁿ) x y ε = ℚ.recompute< ∘ (subst (_< ⟨ ε ⟩₊) $
  abs(x - y)         ≡⟨ sym $ abs- (x - y) ⟩
  abs(- (x - y))     ≡⟨ cong abs (ℚ.·DistL+ -1 x (- y)) ⟩
  abs((- x) - (- y)) ∎)

+ⁿ : NE[ ℚPremetricSpace , NE[ ℚPremetricSpace , ℚPremetricSpace ]PrSpace ]
+ⁿ = NE₂[_,_,_].makeNE₂ +NE₂ module +NE where
  open NE₂[_,_,_]
  open IsNonExpansive
  +NE₂ : NE₂[ ℚPremetricSpace , ℚPremetricSpace , ℚPremetricSpace ]
  fun +NE₂ = _+_
  pres≈ (lNE +NE₂ y) = λ x z ε → ℚ.recompute< ∘ subst ((_< ⟨ ε ⟩₊) ∘ abs)
    (translatedDifference y x z ∙ cong₂ _-_ (+Comm y x) (+Comm y z))
  pres≈ (rNE +NE₂ x) = λ y z ε → ℚ.recompute< ∘ subst ((_< ⟨ ε ⟩₊) ∘  abs)
    (translatedDifference x y z)
