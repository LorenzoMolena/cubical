module Cubical.Algebra.ArchimedeanRing.Base where
{-
  Definition of an archimedean ring.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

import Cubical.Functions.Logic as L

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc) renaming (
  _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _∸_ to _∸ℕ_ ; _^_ to _^ℕ_)
open import Cubical.Data.Nat.Order as ℕ renaming (
  _≤_ to _≤ℕ_ ; _<_ to _<ℕ_)

open import Cubical.Data.Int.Fast as ℤ using (ℤ ; pos ; negsuc ; _ℕ-_) renaming (
  _+_ to _+ℤ_ ; _·_ to _·ℤ_ ; _-_ to _-ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Int.Fast.Order as ℤ renaming (
  _≤_ to _≤ℤ_ ; _<_ to _<ℤ_ )

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Int.Fast

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset hiding (isPseudolattice)
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Binary.Order.Pseudolattice

open import Cubical.Reflection.RecordEquiv

open BinaryRelation

private
  variable
    ℓ ℓ' : Level

record IsArchimedeanRing
  {R : Type ℓ}
  (0r 1r : R )
  (_+_ _·_ : R → R → R)
  (-_ : R → R)
  (_<_ _≤_ : R → R → Type ℓ')
  (ι : ℤ → R) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor isarchimedeanring
  field
    isOrderedCommRing   : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_
    ·CancelR<           : ∀ x y z → 0r < z → (x · z) < (y · z) → x < y
    isMonomorphism      : IsOrderedCommRingMono (str ℤOrderedCommRing) ι
                            (orderedcommringstr _ _ _ _ _ _ _ isOrderedCommRing)
    archimedeanProperty : ∀ x y → 0r < x → 0r < y → ∃[ k ∈ ℕ ] x < (ι (pos (suc k)) · y)

  ι₀₊ : ℕ → R
  ι₀₊ = ι ∘ pos

  ι₊₁ : ℕ → R
  ι₊₁ = ι ∘ pos ∘ suc

  open IsOrderedCommRing isOrderedCommRing hiding (·CancelR<) public
  open IsOrderedCommRingMono isMonomorphism public

  ·CancelL< : ∀ x y z → 0r < z → (z · x) < (z · y) → x < y
  ·CancelL< x y z 0<z = ·CancelR< x y z 0<z ∘ subst2 _<_ (·Comm _ _) (·Comm _ _)

record ArchimedeanRingStr (ℓ' : Level) (R : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor archimedeanringstr
  field
    0r 1r : R
    _+_ _·_ : R → R → R
    -_ : R → R
    _<_ _≤_ : R → R → Type ℓ'
    ι : ⟨ ℤOrderedCommRing ⟩ → R
    isArchimedeanRing : IsArchimedeanRing 0r 1r _+_ _·_ -_ _<_ _≤_ ι

  open IsArchimedeanRing isArchimedeanRing public

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix 4 _<_ _≤_

ArchimedeanRing : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
ArchimedeanRing ℓ ℓ' = TypeWithStr ℓ (ArchimedeanRingStr ℓ')

ArchimedeanRing→OrderedCommRing : ArchimedeanRing ℓ ℓ' → OrderedCommRing ℓ ℓ'
ArchimedeanRing→OrderedCommRing R = _ , orderedcommringstr _ _ _ _ _ _ _ isOrderedCommRing
  where open ArchimedeanRingStr (R .snd)
