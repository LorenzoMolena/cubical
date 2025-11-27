module Cubical.Relation.Premetric.Instances.Rationals.Fast where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Empty as ⊥

open import Cubical.Data.NatPlusOne using ()
open import Cubical.Data.Int.Fast   using ()

open import Cubical.Data.Rationals.Fast.Base
open import Cubical.Data.Rationals.Fast.Properties as ℚ using (max ; min ; maxComm)
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

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Rationals.Fast

open import Cubical.Relation.Binary.Order.QuosetReasoning

open <-≤-Reasoning ℚ (ℚ≤Poset .snd) (ℚ<Quoset .snd)
  (λ x {y z} → isTrans<≤ x y z)
  (λ x {y z} → isTrans≤< x y z)
  (λ   {x y} → <Weaken≤  x y)
open <-syntax
open ≤-syntax
open ≡-syntax

open Positive ℚOrderedCommRing renaming (R₊ to ℚ₊ ; R₊AdditiveSemigroup to +ℚ₊Semigroup)

open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory (ℚOrderedCommRing)
open RingTheory (CommRing→Ring ℚCommRing)


open import Cubical.Relation.Premetric.Base
open PremetricStr

-- lemmas to be replaced with ring solver
private
  -[x-y]≡y-x : ∀ (a b : ℚ) → -(a - b) ≡ b - a
  -[x-y]≡y-x a b = sym (-Dist a (- b)) ∙ (λ i → +Comm (- a) (-Idempotent b i) i)

  x-z≡[x-y]+[y-z] : ∀ (a b c : ℚ) → a - c ≡ (a - b) + (b - c)
  x-z≡[x-y]+[y-z] x y z =
    x - z               ≡⟨ cong (x +_) (sym (+IdL (- z))) ⟩
    x + (0 - z)         ≡⟨ sym $ cong ((x +_) ∘ (_- z)) (+InvL y) ⟩
    x + ((- y + y) - z) ≡⟨ sym $ cong (x +_) (+Assoc (- y) y (- z)) ⟩
    x + (- y + (y - z)) ≡⟨ +Assoc x (- y) ((y - z)) ⟩
    (x - y) + (y - z)   ∎

½ : ℚ
½ = [ 1 / 2 ]

-- lemmas to be replaced for arbitrary OCR with characteristic ≠ 2 (i.e. with ½)

0<½ : 0 < ½
0<½ = 0 , refl

0≤½ : 0 ≤ ½
0≤½ = 1 , refl

mean : ℚ → ℚ → ℚ
mean x y = (x + y) · ½

meanIdem : ∀ x → mean x x ≡ x
meanIdem x =
  (x + x) · ½   ≡⟨ ·DistL+ x x ½ ⟩
  x · ½ + x · ½ ≡⟨ sym $ ·DistR+ x ½ ½ ⟩
  x · (½ + ½)   ≡⟨ cong (x ·_) (eq/ _ _ refl) ⟩
  x · 1         ≡⟨ ·IdR x ⟩
  x             ∎

<→<mean : ∀ (x y : ℚ) → x <ℚ y → x <ℚ mean x y
<→<mean x y x<y = begin<
  x           ≡→≤⟨ sym (meanIdem x) ⟩
  (x + x) · ½   <⟨ ·MonoR< (x + x) (x + y) ½ 0<½ (+MonoL< x y x x<y) ⟩
  (x + y) · ½  ◾

<→mean< : ∀ (x y : ℚ) → x <ℚ y → mean x y <ℚ y
<→mean< x y x<y = begin<
  (x + y) · ½   <⟨ ·MonoR< (x + y) (y + y) ½ 0<½ (+MonoR< x y y x<y) ⟩
  (y + y) · ½ ≡→≤⟨ meanIdem y ⟩
  y             ◾

0≤abs : ∀ z → 0 ≤ℚ abs z
0≤abs z = begin≤
  0                   ≡→≤⟨ sym $ cong (_· ½) (+InvR z) ∙ (0LeftAnnihilates ½) ⟩
  (z - z) · ½           ≤⟨ ·MonoR≤ (z - z) (abs z + abs z) ½ 0≤½ (begin≤
   z - z                ≤⟨ +MonoR≤ z (abs z) (- z) (≤abs z) ⟩
   abs z - z            ≤⟨ +MonoL≤ (- z) (abs z) (abs z) (-≤abs z) ⟩
   abs z + abs z       ◾)⟩
  (abs z + abs z) · ½ ≡→≤⟨ meanIdem (abs z) ⟩
  abs z                ◾

ℚPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
fst ℚPremetricSpace = ℚ
_≈[_]_ (snd ℚPremetricSpace) = λ x ε y → abs (x - y) <ℚ ⟨ ε ⟩₊
isPremetric (snd ℚPremetricSpace) = isPMℚ
  where
    open IsPremetric

    isPMℚ : IsPremetric (λ x ε y → abs (x - y) <ℚ ⟨ ε ⟩₊)
    isPMℚ .isSetM = isSetℚ
    isPMℚ .isProp≈ x y ε = isProp< (abs (x - y)) ⟨ ε ⟩₊
    isPMℚ .isRefl≈ {x} ε = subst ((_<ℚ ⟨ ε ⟩₊) ∘ abs) (sym (+InvR x)) (ε .snd)
    isPMℚ .isSym≈ {x} {y} ε = subst (_<ℚ ⟨ ε ⟩₊) $
      abs (x - y)             ≡⟨⟩
      max (x - y) (- (x - y)) ≡⟨ maxComm (x - y) (- (x - y)) ⟩
      max (- (x - y)) (x - y) ≡⟨ cong₂ max (-[x-y]≡y-x x y) (sym (-[x-y]≡y-x y x)) ⟩
      max (y - x) (- (y - x)) ≡⟨⟩
      abs (y - x)             ∎
    isPMℚ .isSeparated≈ {x} {y} ∀[ε]•<ε =
      equalByDifference x y $ case (discreteℚ (x - y) 0) return (λ _ → x - y ≡ 0) of λ
      { (yes p) → p
      ; (no ¬p) → ⊥.rec $
          isIrrefl< (abs(x - y)) $
          ∀[ε]•<ε (abs(x - y) , #→0<abs (x - y) ∣ inequalityImplies# (x - y) 0 ¬p ∣₁)
      }
    isPMℚ .isTriangular≈ {x} {y} {z} ε δ <ε <δ = begin<
      abs (x - z)               ≡→≤⟨ cong abs (x-z≡[x-y]+[y-z] x y z) ⟩
      abs ((x - y) + (y - z))     ≤⟨ triangularInequality (x - y) (y - z) ⟩
      abs (x - y) + abs (y - z)   <⟨ +MonoR< (abs(x - y)) ⟨ ε ⟩₊ (abs(y - z)) <ε ⟩
      ⟨ ε ⟩₊ + abs (y - z)         <⟨ +MonoL< (abs(y - z)) ⟨ δ ⟩₊ ⟨ ε ⟩₊ <δ ⟩
      ⟨ ε +₊ δ ⟩₊                  ◾
    isPMℚ .isRounded≈ {x} {y} ε <ε = ∣_∣₁ $
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
