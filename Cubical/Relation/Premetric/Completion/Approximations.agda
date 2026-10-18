open import Cubical.Relation.Premetric
open import Cubical.Foundations.Prelude

-- we use this combinations of levels to avoid using `Lift`s when not needed
module Cubical.Relation.Premetric.Completion.Approximations {ℓ} ℓ'
  (M : PremetricSpace ℓ (ℓ-max ℓ ℓ')) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties

open OrderedCommRingReasoning ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Relation.Premetric.Completion.Base M
open import Cubical.Relation.Premetric.Completion.Elim M
open import Cubical.Relation.Premetric.Completion.Properties ℓ' M renaming (
  ℭPremetricSpace to ℭM)

private
  module M where
    open PremetricStr (snd M) public
    open PremetricTheory M public
  module ℭM where
    open PremetricStr (snd ℭM) public
    open PremetricTheory ℭM public

module WithConvexParam (α β : ℚ₊) (is-convex : ⟨ α ⟩₊ ℚ.+ ⟨ β ⟩₊ ≡ 1) where

  ∃approx : (x : ⟨ ℭM ⟩) → (ε : ℚ₊) → ∃[ m ∈ ⟨ M ⟩ ] (ι m ℭM.≈[ ε ] x)
  ∃approx = Elimℭ-Prop.go e where
    open Elimℭ-Prop
    e : Elimℭ-Prop λ x → ∀ ε → ∃[ m ∈ ⟨ M ⟩ ] (ι m ℭM.≈[ ε ] x)
    e .ιA      x       ε = ∣ x , ι-ι (M.isRefl≈ x ε) ∣₁
    e .limA    x xc IH ε = do
      (m , ιm≈xβε) ← IH (β ·₊ ε) (α ·₊ ε)
      let αε+βε≡ε = sym (ℚ.·DistR+ ⟨ α ⟩₊ _ _) ∙∙ congL ℚ._·_ is-convex ∙∙ ℚ.·IdL ⟨ ε ⟩₊
      return (m , ℭM.subst≈ _ _ αε+βε≡ε (ι-lim (β ·₊ ε) xc ιm≈xβε))
    e .isPropA x         = isPropΠ λ _ → squash₁

  showApprox : ⟨ ℭM ⟩ → ℚ₊ → ∥ ⟨ M ⟩ ∥₁
  showApprox = (PT.map fst ∘_) ∘ ∃approx

  -- behaviour of `showApprox` on points of ℭM
  private
    _ : ∀ {x ε} → showApprox (ι x) ε ≡ ∣ x ∣₁
    _ = refl

    _ : ∀ {x : ℚ₊ → ⟨ M ⟩} {xc ε} → showApprox (lim (ι ∘ x) xc) ε ≡ ∣ x (β ·₊ ε) ∣₁
    _ = refl

    _ : ∀ {x : ℚ₊ → ℚ₊ → ⟨ M ⟩} {xc : (δ : ℚ₊) → isCauchy∼ (ι ∘ x δ)} {xc' ε}
      → showApprox (lim (λ δ → lim (ι ∘ x δ) (xc δ)) xc') ε
      ≡ ∣ x (β ·₊ ε) (β ·₊ (α ·₊ ε)) ∣₁
    _ = refl

-- default choice for the parameters :
module Approx½ = WithConvexParam [ 1 / 2 ]₊ [ 1 / 2 ]₊ (eq/ _ _ refl)
