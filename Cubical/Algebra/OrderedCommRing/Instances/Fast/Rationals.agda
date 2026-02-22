module Cubical.Algebra.OrderedCommRing.Instances.Fast.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Data.Nat as ℕ hiding (_+_ ; _·_)
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Fast.Int as ℤ hiding (_+_ ; _-_ ; -_ ; _·_)
import Cubical.Data.Fast.Int.Order as ℤ

open import Cubical.Data.Fast.Rationals as ℚ
  renaming (_+_ to _+ℚ_ ; _-_ to _-ℚ_; -_ to -ℚ_ ; _·_ to _·ℚ_)
open import Cubical.Data.Fast.Rationals.Order
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Fast.Rationals

open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Properties

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Fast.Rationals

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Fast.Rationals

open CommRingStr
open OrderedCommRingStr
open PseudolatticeStr
open StrictOrderStr

ℚOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
fst ℚOrderedCommRing = ℚ
0r  (snd ℚOrderedCommRing) = 0
1r  (snd ℚOrderedCommRing) = 1
_+_ (snd ℚOrderedCommRing) = _+ℚ_
_·_ (snd ℚOrderedCommRing) = _·ℚ_
-_  (snd ℚOrderedCommRing) = -ℚ_
_<_ (snd ℚOrderedCommRing) = _<ℚ_
_≤_ (snd ℚOrderedCommRing) = _≤ℚ_
isOrderedCommRing (snd ℚOrderedCommRing) = isOrderedCommRingℚ
  where
  open IsOrderedCommRing

  isOrderedCommRingℚ : IsOrderedCommRing 0 1 _+ℚ_ _·ℚ_ -ℚ_ _<ℚ_ _≤ℚ_
  isOrderedCommRingℚ .isCommRing      = ℚCommRing .snd .isCommRing
  isOrderedCommRingℚ .isPseudolattice = ℚ≤Pseudolattice .snd .is-pseudolattice
  isOrderedCommRingℚ .isStrictOrder   = ℚ<StrictOrder .snd .isStrictOrder
  isOrderedCommRingℚ .<-≤-weaken      = <Weaken≤
  isOrderedCommRingℚ .≤≃¬>            = λ x y →
    propBiimpl→Equiv (isProp≤ x y) (isProp¬ (y <ℚ x)) (≤→≯  x y) (≮→≥ y x)
  isOrderedCommRingℚ .+MonoR≤         = ≤-+o
  isOrderedCommRingℚ .+MonoR<         = <-+o
  isOrderedCommRingℚ .posSum→pos∨pos  = λ x y → ∣_∣₁ ∘ 0<+ x y
  isOrderedCommRingℚ .<-≤-trans       = isTrans<≤
  isOrderedCommRingℚ .≤-<-trans       = isTrans≤<
  isOrderedCommRingℚ .·MonoR≤         = ≤-·o
  isOrderedCommRingℚ .·MonoR<         = <-·o
  isOrderedCommRingℚ .0<1             = pos<pos tt

module PositiveRationals where
  private
    0<+Closed : ∀ x y → 0 <ℚ x → 0 <ℚ y → 0 <ℚ x +ℚ y
    0<+Closed = SQ.elimProp2 (λ _ _ → isProp→ (isProp→ (isProp< 0 _))) λ
      { (pos (suc n) , _) (pos (suc m) , _) (pos<pos p) (pos<pos q) → pos<pos tt }

    0<·Closed : ∀ x y → 0 <ℚ x → 0 <ℚ y → 0 <ℚ x ·ℚ y
    0<·Closed = SQ.elimProp2 (λ _ _ → isProp→ (isProp→ (isProp< 0 _))) λ
      { (pos (suc n) , _) (pos (suc m) , _) (pos<pos p) (pos<pos q) → pos<pos tt   }

  open Positive ℚOrderedCommRing 0<+Closed 0<·Closed public renaming (
    R₊ to ℚ₊ ; isSetR₊ to isSetℚ₊ ; R₊≡ to ℚ₊≡)

  -- Natural number literals for ℚ

  open import Cubical.Data.Nat.Literals public

  instance
    fromNatℚ₊ : HasFromNat ℚ₊
    fromNatℚ₊ = record { Constraint = λ { zero → ⊥ ; _ → Unit }
                       ; fromNat = λ { (suc n) .fst → [ pos (suc n) / 1 ]
                                     ; (suc n) .snd → pos<pos tt } }

  [_/_]₊ : ℕ₊₁ → ℕ₊₁ → ℚ₊
  [ 1+ n / 1+ m ]₊ = [ pos (suc n) / 1+ m ] , pos<pos tt

  max₊ : ℚ₊ → ℚ₊ → ℚ₊
  fst (max₊ x y) = ℚ.max (fst x) (fst y)
  snd (max₊ x y) = elimProp2
    {P = λ a b → 0 <ℚ a → 0 <ℚ b → 0 <ℚ ℚ.max a b}
    (λ a b → isPropΠ2 λ _ _ → isProp< 0 (ℚ.max a b))
    (λ { (pos (suc n) , 1+ a) (pos (suc m) , 1+ b) (pos<pos p) (pos<pos q) →
    let
      1+n = suc n ; 1+m = suc m ; 1+a = suc a ; 1+b = suc b
    in
      -- NOTE :
      -- if we are only concerned about efficiency, then there is no need to recompute,
      -- as `maxSuc` already reduces efficiently to refl for concrete (large) numbers
      -- however, since `_<_` is an indexed data type, we recompute anyway to avoid
      -- `transpX-_<_` in the normal form
      inj (ℤ.recompute< (subst (0 ℤ.<_)
      (sym $ cong (pos ∘ (ℕ._· 1)) $ maxSuc {predℕ (1+n ℕ.· 1+b)} {predℕ (1+m ℕ.· 1+a)})
      (ℤ.pos<pos tt))) })
    (fst x) (fst y) (snd x) (snd y)

  min₊ : ℚ₊ → ℚ₊ → ℚ₊
  fst (min₊ x y) = ℚ.min (fst x) (fst y)
  snd (min₊ x y) = elimProp2
    {P = λ a b → 0 <ℚ a → 0 <ℚ b → 0 <ℚ ℚ.min a b}
    (λ a b → isPropΠ2 λ _ _ → isProp< 0 (ℚ.min a b))
    (λ { (pos (suc n) , 1+ a) (pos (suc m) , 1+ b) (pos<pos p) (pos<pos q) →
    let
      1+n = suc n ; 1+m = suc m ; 1+a = suc a ; 1+b = suc b
    in
      inj (ℤ.recompute< (subst (0 ℤ.<_)
      (sym $ cong (pos ∘ (ℕ._· 1)) $ minSuc {predℕ (1+n ℕ.· 1+b)} {predℕ (1+m ℕ.· 1+a)})
      (ℤ.pos<pos tt))) })
    (fst x) (fst y) (snd x) (snd y)
