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
open import Cubical.Relation.Binary.Order.Poset hiding (isLattice)
open import Cubical.Relation.Binary.Order.StrictOrder

open BinaryRelation

private
  variable
    ℓ ℓ' : Level

record IsLattice
  {L : Type ℓ} (_≤_ : L → L → Type ℓ') (_⊓_ _⊔_ : L → L → L) : Type (ℓ-max ℓ ℓ') where
  constructor islattice
  field
    is-poset : IsPoset _≤_
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

record IsPseudolattice {L : Type ℓ} (_≤_ : L → L → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor ispseudolattice

  field
    is-poset : IsPoset _≤_
    is-pseudolattice : isPseudolattice (poset L _≤_ is-poset)

  _∧l_ : L → L → L
  a ∧l b = (is-pseudolattice .fst a b) .fst

  _∨l_ : L → L → L
  a ∨l b = (is-pseudolattice .snd a b) .fst

  infixl 7 _∧l_
  infixl 6 _∨l_

record PseudolatticeStr (ℓ' : Level) (L : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor pseudolatticestr

  field
    _≤_ : L → L → Type ℓ'
    is-pseudolattice : IsPseudolattice _≤_

Pseudolattice : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
Pseudolattice ℓ ℓ' = TypeWithStr ℓ (PseudolatticeStr ℓ')

makeIsPseudolattice : {L : Type ℓ} {_≤_ : L → L → Type} {_∨l_ _∧l_ : L → L → L}
                      (is-setL : isSet L)
                      (is-prop-valued : isPropValued _≤_)
                      (is-refl : isRefl _≤_)
                      (is-trans : isTrans _≤_)
                      (is-antisym : isAntisym _≤_)
                      (is-meet-semipseudolattice : isMeetSemipseudolattice (poset L _≤_ (isposet is-setL is-prop-valued is-refl is-trans is-antisym)))
                      (is-join-semipseudolattice : isJoinSemipseudolattice (poset L _≤_ (isposet is-setL is-prop-valued is-refl is-trans is-antisym)))
                      → IsPseudolattice _≤_
makeIsPseudolattice {_≤_ = _≤_} is-setL is-prop-valued is-refl is-trans is-antisym is-meet-semipseudolattice is-join-semipseudolattice = PS
  where
    PS : IsPseudolattice _≤_
    PS .IsPseudolattice.is-poset = isposet is-setL is-prop-valued is-refl is-trans is-antisym
    PS .IsPseudolattice.is-pseudolattice = is-meet-semipseudolattice , is-join-semipseudolattice

record IsOrderedCommRing
  {R : Type ℓ}
  (0r 1r : R )
  (_+_ _·_ : R → R → R)
  (-_ : R → R)
  (_<_ _≤_ : R → R → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor isorderedcommring
  open BinaryRelation
  field
    isCommRing      : IsCommRing 0r 1r _+_ _·_ -_
    isPseudoLattice : IsPseudolattice _≤_
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

  open IsPseudolattice isPseudoLattice renaming (_∧l_ to _⊓_ ; _∨l_ to _⊔_)

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
