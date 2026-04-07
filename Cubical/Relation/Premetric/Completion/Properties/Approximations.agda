module Cubical.Relation.Premetric.Completion.Properties.Approximations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Rationals.Fast.Base as ℚ
import Cubical.Data.Rationals.Fast.Properties as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties

open OrderedCommRingReasoning ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

private
  variable
    ℓ ℓ' : Level

module Show (M' : PremetricSpace ℓ ℓ') where
  open import Cubical.Relation.Premetric.Completion.Base M' renaming (ℭ to ℭM)
  open import Cubical.Relation.Premetric.Completion.Elim M'
  open import Cubical.Relation.Premetric.Completion.Properties.Closeness M' renaming (
    ℭPremetricSpace to ℭM')
  open PremetricTheory ℭM'

  private
    M  = fst M'
    open module PM  = PremetricStr (snd M')
    open module PCM = PremetricStr (snd ℭM')

  module WithConvexParam (α β : ℚ₊) (is-convex : ⟨ α ⟩₊ ℚ.+ ⟨ β ⟩₊ ≡ 1) where

    ∃approx' : (x : ℭM) → (ε : ℚ₊) → ∃[ m ∈ M ] (ι m PCM.≈[ ε ] x)
    ∃approx' = Elimℭ-Prop.go e where
      open Elimℭ-Prop
      e : Elimℭ-Prop _
      ιA      e x       ε = ∣ x , ι-ι x x ε (PM.isRefl≈ x ε) ∣₁
      limA    e x xc IH ε = do
        (m , ιm≈xβε) ← IH (β ·₊ ε) (α ·₊ ε)
        let
          αε+βε≡ε : ⟨ α ·₊ ε +₊ β ·₊ ε ⟩₊ ≡ ⟨ ε ⟩₊
          αε+βε≡ε = sym (ℚ.·DistR+ ⟨ α ⟩₊ ⟨ β ⟩₊ ⟨ ε ⟩₊)
                 ∙∙ cong (ℚ._· ⟨ ε ⟩₊) is-convex
                 ∙∙ ℚ.·IdL ⟨ ε ⟩₊

          ιm≈lim : ι m PCM.≈[ ε ] lim x xc
          ιm≈lim = PCM.subst≈ _ _ αε+βε≡ε (ι-lim+₊ m x (α ·₊ ε) (β ·₊ ε) xc ιm≈xβε)
        return (m , ιm≈lim)
      isPropA e x         = isPropΠ λ _ → squash₁

    show' : ℭM → ℚ₊ → ∥ M ∥₁
    show' = (PT.map fst ∘_) ∘ ∃approx'

    _ : ∀ {x ε} → show' (ι x) ε ≡ ∣ x ∣₁
    _ = refl

    _ : ∀ {x : ℚ₊ → M} {xc ε} → show' (lim (ι ∘ x) xc) ε ≡ ∣ x (β ·₊ ε) ∣₁
    _ = refl

    _ : ∀ {x : ℚ₊ → ℚ₊ → M} {xc : (δ : ℚ₊) → isCauchy (ι ∘ x δ)} {xc' ε}
      → show' (lim (λ δ → lim (ι ∘ x δ) (xc δ)) xc') ε ≡ ∣ x (β ·₊ ε) (β ·₊ (α ·₊ ε)) ∣₁
    _ = refl

  -- default choice for the parameters :
  open WithConvexParam [ 1 / 2 ]₊ [ 1 / 2 ]₊ (eq/ _ _ refl) public renaming (
    ∃approx' to ∃approx ; show' to show)
