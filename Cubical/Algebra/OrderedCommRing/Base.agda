module Cubical.Algebra.OrderedCommRing.Base where
{-
  Definition of an ordered commutative ring.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Reflection.RecordEquiv

import Cubical.Functions.Logic as L

open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing.Base

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset hiding (
  isPseudolattice ; isPropIsPseudolattice)
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Binary.Order.Pseudolattice

open BinaryRelation

private
  variable
    ℓ ℓ' : Level

record IsOrderedCommRing
  {R : Type ℓ}
  (0r 1r : R )
  (_+_ _·_ : R → R → R)
  (-_ : R → R)
  (_<_ _≤_ : R → R → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor isorderedcommring
  field
    isCommRing      : IsCommRing 0r 1r _+_ _·_ -_
    isPseudolattice : IsPseudolattice _≤_
    isStrictOrder   : IsStrictOrder _<_
    <-≤-weaken      : ∀ x y → x < y → x ≤ y
    ≤≃¬>            : ∀ x y → (x ≤ y) ≃ (¬ (y < x))
    +MonoR≤         : ∀ x y z → x ≤ y → (x + z) ≤ (y + z)
    +MonoR<         : ∀ x y z → x < y → (x + z) < (y + z)
    posSum→pos∨pos  : ∀ x y → 0r < (x + y) → (0r < x) L.⊔′ (0r < y)
    <-≤-trans       : ∀ x y z → x < y → y ≤ z → x < z
    ≤-<-trans       : ∀ x y z → x ≤ y → y < z → x < z
    ·MonoR≤         : ∀ x y z → 0r ≤ z → x ≤ y → (x · z) ≤ (y · z)
    ·MonoR<         : ∀ x y z → 0r < z → x < y → (x · z) < (y · z)
    0<1             : 0r < 1r

  open IsCommRing isCommRing public
  open IsPseudolattice isPseudolattice hiding (is-set) renaming (
      is-prop-valued to is-prop-valued≤ ; is-trans to is-trans≤
    ; isPseudolattice to is-pseudolattice
    ; _∧l_ to _⊓_ ; _∨l_ to _⊔_) public
  open IsStrictOrder isStrictOrder hiding (is-set) renaming (
    is-prop-valued to is-prop-valued< ; is-trans to is-trans<) public


unquoteDecl IsOrderedCommRingIsoΣ = declareRecordIsoΣ IsOrderedCommRingIsoΣ (quote IsOrderedCommRing)

record OrderedCommRingStr (ℓ' : Level) (R : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor orderedcommringstr
  field
    0r 1r : R
    _+_ _·_ : R → R → R
    -_ : R → R
    _<_ _≤_ : R → R → Type ℓ'
    isOrderedCommRing : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_

  open IsOrderedCommRing isOrderedCommRing public

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix 4 _<_ _≤_


unquoteDecl OrderedCommRingStrIsoΣ = declareRecordIsoΣ OrderedCommRingStrIsoΣ (quote OrderedCommRingStr)

OrderedCommRing : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedCommRing ℓ ℓ' = TypeWithStr ℓ (OrderedCommRingStr ℓ')

module _ {R : Type ℓ} {0r 1r : R} {_+_ _·_ : R → R → R} { -_ : R → R }
  {_<_ _≤_ : R → R → Type ℓ'}
  (is-setR : isSet R)
  (+Assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
  (+IdR : (x : R) → x + 0r ≡ x)
  (+InvR : (x : R) → x + (- x) ≡ 0r)
  (+Comm : (x y : R) → x + y ≡ y + x)
  (·Assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
  (·IdR : (x : R) → x · 1r ≡ x)
  (·DistR+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
  (·Comm : (x y : R) → x · y ≡ y · x)
  (is-prop-valued≤ : isPropValued _≤_)
  (is-refl : isRefl _≤_)
  (is-trans≤ : isTrans _≤_)
  (is-antisym : isAntisym _≤_)
  (is-meet-semipseudolattice : isMeetSemipseudolattice (
    poset R _≤_ (isposet is-setR is-prop-valued≤ is-refl is-trans≤ is-antisym)))
  (is-join-semipseudolattice : isJoinSemipseudolattice (
    poset R _≤_ (isposet is-setR is-prop-valued≤ is-refl is-trans≤ is-antisym)))
  (is-prop-valued : isPropValued _<_)
  (is-irrefl : isIrrefl _<_)
  (is-trans : isTrans _<_)
  (is-asym : isAsym _<_)
  (is-weakly-linear : isWeaklyLinear _<_)
  (<-≤-weaken : ∀ x y → x < y → x ≤ y)
  (≤≃¬> : ∀ x y → (x ≤ y) ≃ (¬ (y < x)))
  (+MonoR≤ : ∀ x y z → x ≤ y → (x + z) ≤ (y + z))
  (+MonoR< : ∀ x y z → x < y → (x + z) < (y + z))
  (posSum→pos∨pos : ∀ x y → 0r < (x + y) → 0r < x L.⊔′ 0r < y)
  (<-≤-trans : ∀ x y z → x < y → y ≤ z → x < z)
  (≤-<-trans : ∀ x y z → x ≤ y → y < z → x < z)
  (·MonoR≤ : ∀ x y z → 0r ≤ z → x ≤ y → (x · z) ≤ (y · z))
  (·MonoR< : ∀ x y z → 0r < z → x < y → (x · z) < (y · z))
  (0<1 : 0r < 1r) where
  makeIsOrderedCommRing : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_
  makeIsOrderedCommRing = OCR where
    OCR : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_
    IsOrderedCommRing.isCommRing OCR = makeIsCommRing
      is-setR +Assoc +IdR +InvR +Comm ·Assoc ·IdR ·DistR+ ·Comm
    IsOrderedCommRing.isPseudolattice OCR = makeIsPseudolattice
      is-setR is-prop-valued≤ is-refl is-trans≤ is-antisym
      is-meet-semipseudolattice is-join-semipseudolattice
    IsOrderedCommRing.isStrictOrder OCR =
      isstrictorder is-setR is-prop-valued is-irrefl is-trans is-asym is-weakly-linear
    IsOrderedCommRing.<-≤-weaken OCR = <-≤-weaken
    IsOrderedCommRing.≤≃¬> OCR = ≤≃¬>
    IsOrderedCommRing.+MonoR≤ OCR = +MonoR≤
    IsOrderedCommRing.+MonoR< OCR = +MonoR<
    IsOrderedCommRing.posSum→pos∨pos OCR = posSum→pos∨pos
    IsOrderedCommRing.<-≤-trans OCR = <-≤-trans
    IsOrderedCommRing.≤-<-trans OCR = ≤-<-trans
    IsOrderedCommRing.·MonoR≤ OCR = ·MonoR≤
    IsOrderedCommRing.·MonoR< OCR = ·MonoR<
    IsOrderedCommRing.0<1 OCR = 0<1

OrderedCommRing→PseudoLattice : OrderedCommRing ℓ ℓ' → Pseudolattice ℓ ℓ'
OrderedCommRing→PseudoLattice R .fst = R .fst
OrderedCommRing→PseudoLattice R .snd = pseudolatticestr _ isPseudolattice where
  open OrderedCommRingStr (str R)

OrderedCommRing→CommRing : OrderedCommRing ℓ ℓ' → CommRing ℓ
OrderedCommRing→CommRing R .fst = R .fst
OrderedCommRing→CommRing R .snd = commringstr _ _ _ _ _ isCommRing where
  open OrderedCommRingStr (str R)

module _
  {R : Type ℓ}
  (0r 1r : R )
  (_+_ _·_ : R → R → R)
  (-_ : R → R)
  (_<_ _≤_ : R → R → Type ℓ') where

  isPropIsOrderedCommRing : isProp (IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_)
  isPropIsOrderedCommRing = isOfHLevelRetractFromIso 1
    IsOrderedCommRingIsoΣ $
      isPropΣ (isPropIsCommRing 0r 1r _+_ _·_ -_) λ isCR →
      isPropΣ (isPropIsPseudolattice _≤_) λ isPL →
      isPropΣ (isPropIsStrictOrder _<_) λ isSO →
      isProp× (isPropΠ3 λ x y _ → isPL .IsPseudolattice.is-prop-valued _ _) $
      isProp× (isPropΠ2 λ x y       → isOfHLevel≃ 1 (IsPoset.is-prop-valued
                (IsPseudolattice.isPoset isPL) x y) (isProp¬ (y < x))) $
      isProp× (isPropΠ4 λ x y z _   → isPL .IsPseudolattice.is-prop-valued _ _) $
      isProp× (isPropΠ4 λ x y z _   → isSO .IsStrictOrder.is-prop-valued _ _) $
      isProp× (isPropΠ3 λ x y _     → PropTrunc.squash₁) $
      isProp× (isPropΠ5 λ x y z _ _ → IsStrictOrder.is-prop-valued isSO _ _) $
      isProp× (isPropΠ5 λ x y z _ _ → IsStrictOrder.is-prop-valued isSO _ _) $
      isProp× (isPropΠ5 λ x y z _ _ → isPL .IsPseudolattice.is-prop-valued _ _) $
      isProp× (isPropΠ5 λ x y z _ _ → IsStrictOrder.is-prop-valued isSO _ _)
              (IsStrictOrder.is-prop-valued isSO _ _)


module _
  {R : Type ℓ}
  {0r 1r : R}
  {_+_ _·_ : R → R → R}
  { -_ : R → R}
  {_<_ _≤_ : R → R → Type ℓ'} where

  isOrderedCommRing→isProp<≡<' : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_
                               → {_<'_ : R → R → Type ℓ'}
                               → isProp (_<_ ≡ _<'_)
  isOrderedCommRing→isProp<≡<' isOCR< p q i j x y =
    isOfHLevel⁺≡ₗ 0 (is-prop-valued< x y) (λ i → p i x y) (λ i → q i x y) i j
    where open IsOrderedCommRing isOCR<

  isOrderedCommRing→isProp≤≡≤' : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_
                               → {_≤'_ : R → R → Type ℓ'}
                               → isProp (_≤_ ≡ _≤'_)
  isOrderedCommRing→isProp≤≡≤' isOCR≤ p q i j x y =
    isOfHLevel⁺≡ₗ 0 (is-prop-valued≤ x y) (λ i → p i x y) (λ i → q i x y) i j
    where open IsOrderedCommRing isOCR≤

isSetOrderedRingStr : (R : Type ℓ) → isSet (OrderedCommRingStr ℓ' R)
isSetOrderedRingStr R =
  let open OrderedCommRingStr using (is-set)
  in
  isOfHLevelSucIfInhabited→isOfHLevelSuc 1 λ str →
  isOfHLevelRetractFromIso 2 OrderedCommRingStrIsoΣ $
  isSetΣ (str .is-set) λ _ →
  isSetΣ (str .is-set) λ _ →
  isSetΣ (isSet→ (isSet→ (str .is-set))) λ _ →
  isSetΣ (isSet→ (isSet→ (str .is-set))) λ _ →
  isSetΣ (isSet→ (str .is-set)) λ _ →
  λ (_ , _ , OCR<) _ p q →
  ΣSquareSet
    (λ _ → λ (_ , OCR≤) _ r s →
      ΣSquareSet
        (isProp→isSet ∘ isPropIsOrderedCommRing _ _ _ _ _ _)
        (isOrderedCommRing→isProp≤≡≤' OCR≤ (cong fst r) (cong fst s)))
    (isOrderedCommRing→isProp<≡<' OCR< (cong fst p) (cong fst q))
