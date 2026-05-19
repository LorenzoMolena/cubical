module Cubical.Relation.Premetric.Instances.SubSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open PositiveRationals

private
  variable
    ℓM ℓM' ℓ' : Level

module SubSpace
  (M' : PremetricSpace ℓM ℓM')
  (P : ⟨ M' ⟩ → Type ℓ') (is-prop-valued : ∀ x → isProp (P x))
  where
  private
    M = ⟨ M' ⟩
    module M = PremetricStr (snd M')

  infix 5 _≈⊆[_]_
  _≈⊆[_]_ : Σ[ m ∈ M ] P m → ℚ₊ → Σ[ m ∈ M ] P m → Type ℓM'
  x ≈⊆[ ε ] y = fst x M.≈[ ε ] fst y

  isPremetric⊆ : IsPremetric _≈⊆[_]_
  isPremetric⊆ .IsPremetric.isSetM        = isSetΣSndProp M.isSetM is-prop-valued
  isPremetric⊆ .IsPremetric.isProp≈       = λ _ _ _     → M.isProp≈ _ _ _
  isPremetric⊆ .IsPremetric.isRefl≈       = λ _ _       → M.isRefl≈ _ _
  isPremetric⊆ .IsPremetric.isSym≈        = λ _ _ _     → M.isSym≈ _ _ _
  isPremetric⊆ .IsPremetric.isSeparated≈  = λ _ _       → Σ≡Prop is-prop-valued ∘ M.isSeparated≈ _ _
  isPremetric⊆ .IsPremetric.isTriangular≈ = λ _ _ _ _ _ → M.isTriangular≈ _ _ _ _ _
  isPremetric⊆ .IsPremetric.isRounded≈    = λ _ _ _     → M.isRounded≈ _ _ _

  ⊆PremetricSpace : PremetricSpace (ℓ-max ℓM ℓ') ℓM'
  fst ⊆PremetricSpace = Σ M P
  PremetricStr._≈[_]_      (snd ⊆PremetricSpace) = _≈⊆[_]_
  PremetricStr.isPremetric (snd ⊆PremetricSpace) = isPremetric⊆

  ι⊆ⁿ : NE[ ⊆PremetricSpace , M' ]
  fst ι⊆ⁿ = fst
  IsNonExpansive.pres≈ (snd ι⊆ⁿ) = λ _ _ _ → idfun _

  ι⊆ᶜ : C[ ⊆PremetricSpace , M' ]
  ι⊆ᶜ = NE→C ι⊆ⁿ

  ι⊆ᵘᶜ : UC[ ⊆PremetricSpace , M' ]
  ι⊆ᵘᶜ = NE→UC ι⊆ⁿ

  ι⊆ᴸ : L[ ⊆PremetricSpace , M' ]
  ι⊆ᴸ = NE→L ι⊆ⁿ
