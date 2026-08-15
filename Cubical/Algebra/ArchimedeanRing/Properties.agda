module Cubical.Algebra.ArchimedeanRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.ArchimedeanRing.Base
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.Ring

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne as ℕ₊₁ using (ℕ₊₁ ; 1+_ ; ℕ₊₁→ℕ)
open import Cubical.Data.Fast.Int as ℤ using (ℤ ; pos ; negsuc ; neg)
import Cubical.Data.Fast.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Poset hiding (isPseudolattice)
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Nullary

open import Cubical.Tactics.CommRingSolver

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
    0<ι₊₁ a = subst (_< ι₊₁ a) ιpres0 (ιpres< (pos 0) (pos (ℕ₊₁→ℕ a)) ℤ.zero-<possuc)

    0≤ι₀₊ : ∀ a → 0r ≤ ι₀₊ a
    0≤ι₀₊ zero    = subst (_≤ ι₀₊ 0) ιpres0 (is-refl _)
    0≤ι₀₊ (suc a) = <-≤-weaken 0r (ι₊₁ (1+ a)) (0<ι₊₁ (1+ a))

    ¬0≤ιnegsuc : ∀ n → ¬ (0r ≤ ι (negsuc n))
    ¬0≤ιnegsuc n = ⊥.rec ∘ ℤ.¬pos≤negsuc ∘ ιreflect≤ _ _ ∘ subst (_≤ _) (sym ιpres0)

    ¬0<ιneg : ∀ n → ¬ (0r < ι (neg n))
    ¬0<ιneg zero    = ⊥.rec ∘ is-irrefl 0r ∘ subst (_ <_) ιpres0
    ¬0<ιneg (suc n) = ⊥.rec ∘ ℤ.¬pos<negsuc ∘ ιreflect< _ _ ∘ subst (_< _) (sym ιpres0)

    0≤ι→Σℕ : ∀ k → 0r ≤ ι k → Σ[ n ∈ ℕ ] pos n ≡ k
    0≤ι→Σℕ (pos    n) = λ _ → n , refl
    0≤ι→Σℕ (negsuc n) = ⊥.rec ∘ ¬0≤ιnegsuc n

    0<ι→Σℕ₊₁ : ∀ k → 0r < ι k → Σ[ n ∈ ℕ₊₁ ] pos (ℕ₊₁→ℕ n) ≡ k
    0<ι→Σℕ₊₁ (pos zero   ) = ⊥.rec ∘ ¬0<ιneg 0
    0<ι→Σℕ₊₁ (pos (suc n)) = λ _ → 1+ n , refl
    0<ι→Σℕ₊₁ (negsuc n   ) = ⊥.rec ∘ ¬0<ιneg (suc n)

    archimedeanPropertyℕ₊₁ : ∀ x y → 0r ≤ x → 0r < y → ∃[ n ∈ ℕ₊₁ ] x < ι₊₁ n · y
    archimedeanPropertyℕ₊₁ x y 0≤x 0<y = do
      (k , x<ιky) ← archimedeanProperty x y 0<y
      let
        0<ιk = 0r < ι k
        0<ιk = ·CancelR< 0r (ι k) y 0<y
          (subst (_< ι k · y) (sym (0LeftAnnihilates y)) (≤-<-trans 0r x _ 0≤x x<ιky))
      return (map-snd (flip (subst ((x <_) ∘ (_· y) ∘ ι)) x<ιky ∘ sym) (0<ι→Σℕ₊₁ k 0<ιk))

    ∃ℤUpperBound : ∀ x → ∃[ k ∈ ℤ ] x < ι k
    ∃ℤUpperBound x = do
      (k , x<ιk·1) ← archimedeanProperty x 1r 0<1
      return (k , subst (x <_) (·IdR (ι k)) x<ιk·1)

    ∃ℤLowerBound : ∀ x → ∃[ k ∈ ℤ ] ι k < x
    ∃ℤLowerBound x = do
      (k , -x<ιk) ← ∃ℤUpperBound (- x)
      return (ℤ.- k , subst2 _<_ (sym (ιpres- k)) (solve! RCR) (-Flip< (- x) (ι k) -x<ιk))
