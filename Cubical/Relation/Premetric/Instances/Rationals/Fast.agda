module Cubical.Relation.Premetric.Instances.Rationals.Fast where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Empty as ⊥

open import Cubical.Data.NatPlusOne using ()
open import Cubical.Data.Int.Fast   using ()

open import Cubical.Data.Rationals.Fast.Base
open import Cubical.Data.Rationals.Fast.Order renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Algebra.Ring

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals.Fast

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Poset.Instances.Rationals.Fast

open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.Quoset.Instances.Rationals.Fast

open import Cubical.Relation.Binary.Order.QuosetReasoning

open <-≤-Reasoning ℚ (ℚ≤Poset .snd) (ℚ<Quoset .snd)
  (λ x {y z} → isTrans<≤ x y z)
  (λ x {y z} → isTrans≤< x y z)
  (λ   {x y} → <Weaken≤  x y)
open <-syntax
open ≤-syntax
open ≡-syntax

open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory (ℚOrderedCommRing)
open Charactersitic≠2 ℚOrderedCommRing [ 1 / 2 ] (eq/ _ _ refl)
open RingTheory (CommRing→Ring ℚCommRing)


open import Cubical.Relation.Premetric.Base
open PremetricStr

ℚPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
fst ℚPremetricSpace = ℚ
_≈[_]_ (snd ℚPremetricSpace) = λ x ε y → abs (x - y) <ℚ ⟨ ε ⟩₊
isPremetric (snd ℚPremetricSpace) = isPMℚ
  where
    open IsPremetric

    isPMℚ : IsPremetric _
    isPMℚ .isSetM = isSetℚ
    isPMℚ .isProp≈ x y ε = isProp< (abs (x - y)) ⟨ ε ⟩₊
    isPMℚ .isRefl≈ x ε = subst ((_<ℚ ⟨ ε ⟩₊) ∘ abs) (sym (+InvR x)) (ε .snd)
    isPMℚ .isSym≈ x y ε = subst (_<ℚ ⟨ ε ⟩₊) $ abs-Comm x y
    isPMℚ .isSeparated≈ = selfSeparated
    isPMℚ .isTriangular≈ x y z ε δ <ε <δ = begin<
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

        δ<ε : ⟨ δ ⟩₊ <ℚ ⟨ ε ⟩₊
        δ<ε = <→mean< (abs(x - y)) ⟨ ε ⟩₊ <ε

        ∣x-y∣<δ : abs(x - y) <ℚ ⟨ δ ⟩₊
        ∣x-y∣<δ = <→<mean (abs(x - y)) ⟨ ε ⟩₊ <ε
      in
        δ , δ<ε , ∣x-y∣<δ
