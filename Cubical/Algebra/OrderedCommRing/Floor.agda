module Cubical.Algebra.OrderedCommRing.Floor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Fast.Int renaming
  (ℤOrderedCommRing to ℤOCR)
open import Cubical.Algebra.OrderedCommRing.Morphisms

open import Cubical.Data.Fast.Int.Base as ℤ hiding (_+_ ; _-_ ; -_ ; _·_)
open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓ' : Level

-- `OrderedCommRingMono ℤOCR R` is contractible, but we keep it as part of the data,
-- as for specific OCR, there are more efficient implementation for this funciton,
-- rather than iteratively summing the unit of the ring.
-- For instance, with R = ℚ , the underlying function is just λ n → [ n / 1 ]
module FloorCeil (R : OrderedCommRing ℓ ℓ') (ι : OrderedCommRingMono ℤOCR R) where
  open OrderedCommRingStr (str R)

  record Floor (r : ⟨ R ⟩) : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    field
      ⌊_⌋    : ℤ
      ⌊⌋≤    : fst ι ⌊_⌋ ≤ r
      <suc⌊⌋ : r < fst ι (1 ℤ.+ ⌊_⌋)

  record Ceil (r : ⟨ R ⟩) : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    field
      ⌈_⌉     : ℤ
      ≤⌈⌉     : r ≤ fst ι ⌈_⌉
      pred⌈⌉< : fst ι (-1 ℤ.+ ⌈_⌉) < r
