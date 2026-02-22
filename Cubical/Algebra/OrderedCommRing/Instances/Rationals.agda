module Cubical.Algebra.OrderedCommRing.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Data.Nat as ℕ hiding (_+_ ; _·_)
open import Cubical.Data.NatPlusOne as ℕ₊₁
-- to be replaced with fast integers once we have fast rationals
open import Cubical.Data.Int as ℤ hiding (_+_ ; _-_ ; -_ ; _·_)
import Cubical.Data.Int.Order as ℤ

open import Cubical.Data.Rationals as ℚ
  renaming (_+_ to _+ℚ_ ; _-_ to _-ℚ_; -_ to -ℚ_ ; _·_ to _·ℚ_)
open import Cubical.Data.Rationals.Order
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals

open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Properties

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Rationals

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Rationals

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
    propBiimpl→Equiv (isProp≤ x y) (isProp¬ (y <ℚ x)) (≤→≯ x y) (≮→≥ y x)
  isOrderedCommRingℚ .+MonoR≤         = ≤-+o
  isOrderedCommRingℚ .+MonoR<         = <-+o
  isOrderedCommRingℚ .posSum→pos∨pos  = λ x y → ∣_∣₁ ∘ 0<+ x y
  isOrderedCommRingℚ .<-≤-trans       = isTrans<≤
  isOrderedCommRingℚ .≤-<-trans       = isTrans≤<
  isOrderedCommRingℚ .·MonoR≤         = ≤-·o
  isOrderedCommRingℚ .·MonoR<         = <-·o
  isOrderedCommRingℚ .0<1             = isRefl≤ 1

  module PositiveRationals where

    private
      0<+Closed : ∀ x y → 0 <ℚ x → 0 <ℚ y → 0 <ℚ x +ℚ y
      0<+Closed = SQ.elimProp2 (λ x y → isProp→ $ isProp→ $ isProp< 0 $ x +ℚ y) λ
        { (pos zero    , _) _ 0<x _ → ⊥.rec (ℤ.isIrrefl< 0<x)
        ; (negsuc n    , _) _ 0<x _ → ⊥.rec $
          ℤ.¬pos≤negsuc {0} {n} $ ℤ.<-weaken $ subst (0 ℤ.<_) (ℤ.·IdR _) 0<x
        ; (pos (suc n) , _) (pos zero    , _) _ 0<y → ⊥.rec (ℤ.isIrrefl< 0<y)
        ; (pos (suc n) , _) (negsuc m    , _) _ 0<y → ⊥.rec $
          ℤ.¬pos≤negsuc {0} {m} $ ℤ.<-weaken $ subst (0 ℤ.<_) (ℤ.·IdR _) 0<y
        ; (pos (suc n) , 1+ a) (pos (suc m) , 1+ b) _ 0<y →
          subst (0 ℤ.<_)
                (  pos+ (suc n ℕ.· suc b) (suc m ℕ.· suc a)
                ∙∙ cong₂ ℤ._+_ (ℤ.pos·pos (suc n) (suc b)) (ℤ.pos·pos (suc m) (suc a))
                ∙∙ sym (ℤ.·IdR _))
                (ℤ.suc-≤-suc ℤ.zero-≤pos) }

      0<·Closed : ∀ x y → 0 <ℚ x → 0 <ℚ y → 0 <ℚ x ·ℚ y
      0<·Closed = SQ.elimProp2 (λ x y → isProp→ $ isProp→ $ isProp< 0 $ x ·ℚ y) λ
        { (pos zero    , a) _ 0<x _ → ⊥.rec (ℤ.isIrrefl< 0<x)
        ; (negsuc n    , a) _ 0<x _ → ⊥.rec $
          ℤ.¬pos≤negsuc {0} {n} $ ℤ.<-weaken $ subst (0 ℤ.<_) (ℤ.·IdR _) 0<x
        ; (pos (suc n) , a) (pos zero    , b) _ 0<y → ⊥.rec (ℤ.isIrrefl< 0<y)
        ; (pos (suc n) , a) (negsuc m    , b) _ 0<y → ⊥.rec $
          ℤ.¬pos≤negsuc {0} {m} $ ℤ.<-weaken $ subst (0 ℤ.<_) (ℤ.·IdR _) 0<y
        ; (pos (suc n) , a) (pos (suc m) , b) 0<x 0<y →
          subst (0 ℤ.<_)
                (pos·pos (suc n) (suc m) ∙ sym (ℤ.·IdR _))
                (ℤ.suc-≤-suc ℤ.zero-≤pos) }

    open Positive ℚOrderedCommRing 0<+Closed 0<·Closed renaming (
      R₊ to ℚ₊ ; isSetR₊ to isSetℚ₊ ; R₊≡ to ℚ₊≡) public

    -- Natural number literals for ℚ

    open import Cubical.Data.Nat.Literals public

    instance
      fromNatℚ₊ : HasFromNat ℚ₊
      fromNatℚ₊ = record { Constraint = λ { zero → ⊥ ; _ → Unit }
                         ; fromNat = λ
                         { (suc n) .fst → [ pos (suc n) / 1 ]
                         ; (suc n) .snd → subst (0 ℤ.<_)
                                                (sym (ℤ.·IdR (pos (suc n))))
                                                (ℤ.suc-≤-suc ℤ.zero-≤pos) } }

    [_/_]₊ : ℕ₊₁ → ℕ₊₁ → ℚ₊
    [ 1+ n / 1+ m ]₊ .fst = [ pos (suc n) / 1+ m ]
    [ 1+ n / 1+ m ]₊ .snd = subst (0 ℤ.<_)
                                  (sym (ℤ.·IdR (pos (suc n))))
                                  (ℤ.suc-≤-suc ℤ.zero-≤pos)
