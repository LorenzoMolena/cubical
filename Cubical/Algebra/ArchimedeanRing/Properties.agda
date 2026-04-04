module Cubical.Algebra.ArchimedeanRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.ArchimedeanRing.Base
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.Ring

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.Fast.Int as ℤ using (ℤ ; pos)
import Cubical.Data.Fast.Int.Order as ℤ

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Poset hiding (isPseudolattice)
open import Cubical.Relation.Binary.Order.Pseudolattice

private
  variable
    ℓ ℓ' : Level

ArchimedeanRing→StrictOrder : ArchimedeanRing ℓ ℓ' → StrictOrder ℓ ℓ'
ArchimedeanRing→StrictOrder = OrderedCommRing→StrictOrder ∘ ArchimedeanRing→OrderedCommRing

ArchimedeanRing→CommRing : ArchimedeanRing ℓ ℓ' → CommRing ℓ
ArchimedeanRing→CommRing = OrderedCommRing→CommRing ∘ ArchimedeanRing→OrderedCommRing

ArchimedeanRing→Ring : ArchimedeanRing ℓ ℓ' → Ring ℓ
ArchimedeanRing→Ring = OrderedCommRing→Ring ∘ ArchimedeanRing→OrderedCommRing

ArchimedeanRing→PseudoLattice : ArchimedeanRing ℓ ℓ' → Pseudolattice ℓ ℓ'
ArchimedeanRing→PseudoLattice = OrderedCommRing→PseudoLattice ∘ ArchimedeanRing→OrderedCommRing

ArchimedeanRing→Poset : ArchimedeanRing ℓ ℓ' → Poset ℓ ℓ'
ArchimedeanRing→Poset = OrderedCommRing→Poset ∘ ArchimedeanRing→OrderedCommRing

ArchimedeanRing→Quoset : ArchimedeanRing ℓ ℓ' → Quoset ℓ ℓ'
ArchimedeanRing→Quoset = OrderedCommRing→Quoset ∘ ArchimedeanRing→OrderedCommRing

ArchimedeanRing→Apartness : ArchimedeanRing ℓ ℓ' → Apartness ℓ ℓ'
ArchimedeanRing→Apartness = OrderedCommRing→Apartness ∘ ArchimedeanRing→OrderedCommRing

module _ (R' : ArchimedeanRing ℓ ℓ') where
  private
    R = fst R'
    ROCR = ArchimedeanRing→OrderedCommRing R'
    RCR  = ArchimedeanRing→CommRing R'

  open RingTheory (ArchimedeanRing→Ring R')
  open ArchimedeanRingStr (snd R')

  open module ArchimedeanRingReasoning = OrderedCommRingReasoning ROCR

  module ArchimedeanRingTheory where
    open OrderedCommRingTheory ROCR public

    ·CancelL< : ∀ x y z → 0r < z → (z · x) < (z · y) → x < y
    ·CancelL< x y z 0<z = ·CancelR< x y z 0<z ∘ subst2 _<_ (·Comm _ _) (·Comm _ _)

    0<ι₊₁ : ∀ a → 0r < ι₊₁ a
    0<ι₊₁ a = subst (_< ι₊₁ a) ιpres0 (ιpres< (pos 0) (pos (suc a)) ℤ.zero-<possuc)

    0≤ι₀₊ : ∀ a → 0r ≤ ι₀₊ a
    0≤ι₀₊ zero    = subst (_≤ ι₀₊ 0) ιpres0 (is-refl _)
    0≤ι₀₊ (suc a) = <-≤-weaken 0r (ι₊₁ a) (0<ι₊₁ a)
