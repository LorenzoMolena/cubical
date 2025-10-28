module Cubical.Algebra.OrderedCommRing.Instances.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Int as ℤ
  renaming (_+_ to _+ℤ_ ; _-_ to _-ℤ_; -_ to -ℤ_ ; _·_ to _·ℤ_)
open import Cubical.Data.Int.Order
  renaming (_<_ to _<ℤ_ ; _≤_ to _≤ℤ_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int

open import Cubical.Algebra.OrderedCommRing

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Int

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Int

open CommRingStr
open OrderedCommRingStr
open PseudolatticeStr
open StrictOrderStr

ℤOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
fst ℤOrderedCommRing = ℤ
0r  (snd ℤOrderedCommRing) = 0
1r  (snd ℤOrderedCommRing) = 1
_+_ (snd ℤOrderedCommRing) = _+ℤ_
_·_ (snd ℤOrderedCommRing) = _·ℤ_
-_  (snd ℤOrderedCommRing) = -ℤ_
_<_ (snd ℤOrderedCommRing) = _<ℤ_
_≤_ (snd ℤOrderedCommRing) = _≤ℤ_
isOrderedCommRing (snd ℤOrderedCommRing) = makeIsOrderedCommRing'
  (ℤCommRing .snd .isCommRing)
  (ℤ≤Pseudolattice .snd .is-pseudolattice)
  (ℤ<StrictOrder .snd .isStrictOrder)
  (λ _ _ → <-weaken)
  (λ x y → propBiimpl→Equiv isProp≤ (isProp¬ (y <ℤ x))
    (λ x≤y y<x → isIrrefl< (≤<-trans x≤y y<x))
    (λ ¬y<x → case x ≟ y return (λ _ → x ≤ℤ y) of λ {
      (lt x<y) → <-weaken x<y ;
      (eq x≡y) → subst (x ≤ℤ_) x≡y isRefl≤ ;
      (gt y<z) → ⊥.rec (¬y<x y<z) }))
  (λ _ _ z → ≤-+o {o = z})
  (λ _ _ z → <-+o {o = z})
  (λ _ _ _ → <≤-trans)
  (λ _ _ _ → ≤<-trans)
  (λ _ _ _ → 0≤o→≤-·o) (λ _ _ _ → 0<o→<-·o)
  isRefl≤
