module Cubical.Algebra.ArchimedeanRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP using (TypeWithStr)
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Functions.Logic as L

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ renaming (
  _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _∸_ to _∸ℕ_ ; _^_ to _^ℕ_)

open import Cubical.Data.Int.Fast as ℤ using (ℤ ; pos ; negsuc ; _ℕ-_) renaming (
  _+_ to _+ℤ_ ; _·_ to _·ℤ_ ; _-_ to _-ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Int.Fast.Order as ℤ renaming (
  _≤_ to _≤ℤ_ ; _<_ to _<ℤ_ )

open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semiring
open import Cubical.Algebra.Semiring.BigOps
open import Cubical.Algebra.CommSemiring
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Int.Fast
open import Cubical.Algebra.ArchimedeanRing.Base

open import Cubical.Tactics.CommRingSolver

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Poset hiding (isPseudolattice)
open import Cubical.Relation.Binary.Order.Pseudolattice

open import Cubical.Relation.Binary.Order.QuosetReasoning


private
  variable
    ℓ ℓ' ℓ'' : Level

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
  open ArchimedeanRingStr (snd R')
  open RingTheory (ArchimedeanRing→Ring R')
  open JoinProperties (ArchimedeanRing→PseudoLattice R') renaming (
    L≤∨ to L≤⊔ ; R≤∨ to R≤⊔ ; ∨Comm to ⊔Comm ; ∨Idem to ⊔Idem ; ∨LUB to ⊔LUB)

  open OrderedCommRingReasoning ROCR

  module ArchimedeanRingTheory where
    open OrderedCommRingTheory ROCR public
    open BinaryRelation

    0<ι₊₁ : ∀ a → 0r < ι₊₁ a
    0<ι₊₁ a = subst (_< ι₊₁ a) pres0 (pres< 0 (pos (suc a)) ℤ.zero-<possuc)

    0≤ι₀₊ : ∀ a → 0r ≤ ι₀₊ a
    0≤ι₀₊ zero    = subst (_≤ ι₀₊ 0) pres0 (is-refl _)
    0≤ι₀₊ (suc a) = <-≤-weaken 0r (ι₊₁ a) (0<ι₊₁ a)
