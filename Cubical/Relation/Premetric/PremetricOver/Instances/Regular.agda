module Cubical.Relation.Premetric.PremetricOver.Instances.Regular where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.OrderedCommRing

open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓR ℓR' : Level

module _ (R' : OrderedCommRing ℓR ℓR') (0<+Closed : _) (0<·Closed : _) where
  private
    R = fst R'
    RCR = OrderedCommRing→CommRing R'

  open import Cubical.Relation.Premetric.PremetricOver.Base R' 0<+Closed 0<·Closed
  open OrderedCommRingReasoning R'
  open OrderedCommRingStr (snd R') renaming (is-set to isSetR)
  open OrderedCommRingTheory R'
  open Positive R' 0<+Closed 0<·Closed

  module _ (1/2 : R) (p : 1/2 · (1r + 1r) ≡ 1r) where
    open Characteristic≠2 R' 1/2 p
    open R-PremetricStr

    RegularPremetricSpace : R-PremetricSpace ℓR ℓR'
    fst RegularPremetricSpace = R
    _≈[_]_ (snd RegularPremetricSpace) = λ x r y → abs(x - y) < ⟨ r ⟩₊
    isPremetricOver (snd RegularPremetricSpace) = isPMR
      where
        open IsPremetricOver

        isPMR : IsPremetricOver _
        isPMR .isSetM        = isSetR
        isPMR .isProp≈       = λ _ _ _ → is-prop-valued< _ _
        isPMR .isRefl≈       = λ x r → begin<
          abs(x - x) ≡→≤⟨ cong abs (solve! RCR) ∙ abs0 ⟩
          0r           <⟨ snd r ⟩
          ⟨ r ⟩₊       ◾
        isPMR .isSym≈        = λ x y r → subst (_< ⟨ r ⟩₊) (abs-Comm x y)
        isPMR .isSeparated≈  = selfSeparated
        isPMR .isTriangular≈ = λ x y z r s ∣x-y∣<r ∣y-z∣<s → begin<
          abs(x - z)              ≤⟨ triangularInequality- x z y ⟩
          abs(x - y) + abs(y - z) <⟨ +Mono< _ _ _ _ ∣x-y∣<r ∣y-z∣<s ⟩
          ⟨ r +₊ s ⟩₊             ◾
        isPMR .isRounded≈    = λ x y r <r → ∣_∣₁ $
          let
            s : R₊
            s = mean (abs(x - y)) ⟨ r ⟩₊ , (begin<
              0r                       ≤⟨ 0≤abs (x - y) ⟩
              abs(x - y)               <⟨ <→<mean (abs(x - y)) ⟨ r ⟩₊ <r ⟩
              mean (abs(x - y)) ⟨ r ⟩₊ ◾)

            s<r : ⟨ s ⟩₊ < ⟨ r ⟩₊
            s<r = <→mean< (abs(x - y)) ⟨ r ⟩₊ <r

            ∣x-y∣<s : abs(x - y) < ⟨ s ⟩₊
            ∣x-y∣<s = <→<mean (abs(x - y)) ⟨ r ⟩₊ <r
          in
            s , s<r , ∣x-y∣<s
