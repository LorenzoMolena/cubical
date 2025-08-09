module Cubical.Algebra.OrderedCommRing.Base where
{-
  Definition of an commutative ordered ring.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP using (TypeWithStr)
open import Cubical.Foundations.Structure using (⟨_⟩; str)

open import Cubical.Functions.Logic using () renaming (_⊔′_ to _∨_)

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing.Base

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset hiding (isLattice) renaming (isPseudolattice to pseudolattice)
open import Cubical.Relation.Binary.Order.StrictOrder

open BinaryRelation

private
  variable
    ℓ ℓ' : Level

record IsLattice
  {L : Type ℓ} (_≤_ : L → L → Type ℓ') (_⊓_ _⊔_ : L → L → L) : Type (ℓ-max ℓ ℓ') where
  constructor islattice
  field
    isPoset : IsPoset _≤_
    ⊓-inf   : ∀ x y z → z ≤ x → z ≤ y → z ≤ (x ⊓ y)
    ⊔-sup   : ∀ x y z → x ≤ z → y ≤ z → (x ⊔ y) ≤ z

record LatticeStr (ℓ' : Level) (L : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor latticestr
  field
    _≤_ : L → L → Type ℓ'
    _⊓_ _⊔_ : L → L → L
    isLattice : IsLattice _≤_ _⊓_ _⊔_

  infixl 7 _⊓_
  infixl 6 _⊔_
  infixl 4 _≤_

Lattice : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
Lattice ℓ ℓ' = TypeWithStr ℓ (LatticeStr ℓ')

record IsPseudoLattice {L : Type ℓ} (_≤_ : L → L → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor ispseudolattice

  field
    isPoset : IsPoset _≤_
    isPseudoLattice : pseudolattice (poset L _≤_ isPoset)

  _∧l_ : L → L → L
  a ∧l b = (isPseudoLattice .fst a b) .fst

  _∨l_ : L → L → L
  a ∨l b = (isPseudoLattice .snd a b) .fst

  infixl 7 _∧l_
  infixl 6 _∨l_

record PseudoLatticeStr (ℓ' : Level) (L : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor pseudolatticestr

  field
    _≤_ : L → L → Type ℓ'
    isPseudoLattice : IsPseudoLattice _≤_

PseudoLattice : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
PseudoLattice ℓ ℓ' = TypeWithStr ℓ (PseudoLatticeStr ℓ')

record IsOrderedCommRing
  {R : Type ℓ}
  (0r 1r : R )
  (_+_ _·_ : R → R → R)
  (-_ : R → R)
  (_<_ _≤_ : R → R → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor isorderedcommring
  -- open BinaryRelation
  field
    isCommRing      : IsCommRing 0r 1r _+_ _·_ -_
    isPseudoLattice : IsPseudoLattice _≤_
    isStrictOrder   : IsStrictOrder _<_
    ≤≃¬flip<        : ∀ x y → (x ≤ y) ≃ (¬ (y < x)) -- Do we need it? fix the Level?
    +MonoR≤         : ∀ x y z → x ≤ y → (x + z) ≤ (y + z)
    +MonoR<         : ∀ x y z → x < y → (x + z) < (y + z)
    posSum→pos∨pos  : ∀ x y → 0r < (x + y) → 0r < x ∨ 0r < y -- Do we need it?
    <-≤-trans       : ∀ x y z → x < y → y ≤ z → x < z
    ≤-<-trans       : ∀ x y z → x ≤ y → y < z → x < z
    ·MonoR≤         : ∀ x y z → 0r ≤ z → x ≤ y → (x · z) ≤ (y · z)
    ·MonoR<         : ∀ x y z → 0r < z → x < y → (x · z) < (y · z)
    0<1             : 0r < 1r

  open IsPseudoLattice isPseudoLattice renaming (_∧l_ to _⊓_ ; _∨l_ to _⊔_)

record OrderedCommRingStr (ℓ' : Level) (R : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor orderedcommringstr
  field
    0r 1r : R
    _+_ _·_ : R → R → R
    -_ : R → R
    _<_ _≤_ : R → R → Type ℓ'
    isOrderedCommRing : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_

  open IsOrderedCommRing isOrderedCommRing renaming () public

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix 4 _<_ _≤_

OrderedCommRing : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedCommRing ℓ ℓ' = TypeWithStr ℓ (OrderedCommRingStr ℓ')

module _ {R : Type ℓ} {0r 1r : R} {_+_ _·_ : R → R → R} { -_ : R → R }
  { _<_ _≤_ : R → R → Type ℓ' }
  (is-setR : isSet R)
  (+Assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
  (+IdR : (x : R) → x + 0r ≡ x)
  (+InvR : (x : R) → x + (- x) ≡ 0r)
  (+Comm : (x y : R) → x + y ≡ y + x)
  (·Assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
  (·IdR : (x : R) → x · 1r ≡ x)
  (·DistR+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
  (AnnihilL : (x : R) → 0r · x ≡ 0r)
  (·Comm : (x y : R) → x · y ≡ y · x)
  (isPseudoLattice : IsPseudoLattice _≤_)
  (is-prop-valued : isPropValued _<_)
  (is-irrefl : isIrrefl _<_)
  (is-trans : isTrans _<_)
  (is-asym : isAsym _<_)
  (is-weakly-linear : isWeaklyLinear _<_)
  (≤≃¬flip< : ∀ x y → (x ≤ y) ≃ (¬ (y < x)))
  (+MonoR≤ : ∀ x y z → x ≤ y → (x + z) ≤ (y + z))
  (+MonoR< : ∀ x y z → x < y → (x + z) < (y + z))
  (posSum→pos∨pos : ∀ x y → 0r < (x + y) → 0r < x ∨ 0r < y)
  (<-≤-trans : ∀ x y z → x < y → y ≤ z → x < z)
  (≤-<-trans : ∀ x y z → x ≤ y → y < z → x < z)
  (·MonoR≤ : ∀ x y z → 0r ≤ z → x ≤ y → (x · z) ≤ (y · z))
  (·MonoR< : ∀ x y z → 0r < z → x < y → (x · z) < (y · z))
  (0<1 : 0r < 1r) where
  makeIsOrderedCommRing : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_
  makeIsOrderedCommRing = OCR where
    OCR : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_
    IsOrderedCommRing.isCommRing OCR =
      makeIsCommRing is-setR +Assoc +IdR +InvR +Comm ·Assoc ·IdR ·DistR+ ·Comm
    IsOrderedCommRing.isPseudoLattice OCR = isPseudoLattice
    IsOrderedCommRing.isStrictOrder OCR =
      isstrictorder is-setR is-prop-valued is-irrefl is-trans is-asym is-weakly-linear
    IsOrderedCommRing.≤≃¬flip< OCR = ≤≃¬flip<
    IsOrderedCommRing.+MonoR≤ OCR = +MonoR≤
    IsOrderedCommRing.+MonoR< OCR = +MonoR<
    IsOrderedCommRing.posSum→pos∨pos OCR = posSum→pos∨pos
    IsOrderedCommRing.<-≤-trans OCR = <-≤-trans
    IsOrderedCommRing.≤-<-trans OCR = ≤-<-trans
    IsOrderedCommRing.·MonoR≤ OCR = ·MonoR≤
    IsOrderedCommRing.·MonoR< OCR = ·MonoR<
    IsOrderedCommRing.0<1 OCR = 0<1

OrderedCommRing→PseudoLattice : OrderedCommRing ℓ ℓ' → PseudoLattice ℓ ℓ'
OrderedCommRing→PseudoLattice R .fst = R .fst
OrderedCommRing→PseudoLattice R .snd = pseudolatticestr _ isPseudoLattice where
  open OrderedCommRingStr (str R)

OrderedCommRing→CommRing : OrderedCommRing ℓ ℓ' → CommRing ℓ
OrderedCommRing→CommRing R .fst = R .fst
OrderedCommRing→CommRing R .snd = commringstr _ _ _ _ _ isCommRing where
  open OrderedCommRingStr (str R)
