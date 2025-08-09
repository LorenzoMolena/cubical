module Cubical.Algebra.OrderedCommRing.Base where
{-
  Definition of an commutative ordered ring.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP using (TypeWithStr)
open import Cubical.Foundations.Structure using (⟨_⟩; str)

open import Cubical.Functions.Logic using () renaming (_⊔′_ to _∨_)

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing.Base

-- open import Cubical.Algebra.Lattice

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset renaming
  (isLattice to isBoundedLattice)
open import Cubical.Relation.Binary.Order.StrictOrder

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

record IsOrderedCommRing
  {R : Type ℓ}
  (0r 1r : R )
  (_+_ _·_ : R → R → R)
  (-_ : R → R)
  (_<_ _≤_ : R → R → Type ℓ')
  (_⊓_ _⊔_ : R → R → R) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor isorderedcommring
  open BinaryRelation
  field
    isCommRing     : IsCommRing 0r 1r _+_ _·_ -_
    isLattice      : IsLattice _≤_ _⊓_ _⊔_
    isStrictOrder  : IsStrictOrder _<_
    ≤⇔¬<          : ∀ x y → (x ≤ y) ≡ (¬ (y < x)) -- Do we need it? fix the Level?
    +MonoR≤        : ∀ x y z → x ≤ y → (x + z) ≤ (y + z)
    +MonoR<        : ∀ x y z → x < y → (x + z) < (y + z)
    posSum→pos∨pos : ∀ x y → 0r < (x + y) → 0r < x ∨ 0r < y -- Do we need it?
    <-≤-trans      : ∀ x y z → x < y → y ≤ z → x < z
    ≤-<-trans      : ∀ x y z → x ≤ y → y < z → x < z
    ·MonoR≤        : ∀ x y z → 0r ≤ z → x ≤ y → (x · z) ≤ (y · z)
    ·MonoR<        : ∀ x y z → 0r < z → x < y → (x · z) < (y · z)
    0<1            : 0r < 1r

record OrderedCommRingStr (ℓ' : Level) (R : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor orderedcommringstr
  field
    0r 1r : R
    _+_ _·_ : R → R → R
    -_ : R → R
    _<_ _≤_ : R → R → Type ℓ'
    _⊓_ _⊔_ : R → R → R
    isOrderedCommRing : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_ _⊓_ _⊔_

  open IsOrderedCommRing isOrderedCommRing public

  infix  8 -_
  infixl 7 _·_ _⊓_
  infixl 6 _+_ _⊔_
  infix 4 _<_ _≤_

OrderedCommRing : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedCommRing ℓ ℓ' = TypeWithStr ℓ (OrderedCommRingStr ℓ')
