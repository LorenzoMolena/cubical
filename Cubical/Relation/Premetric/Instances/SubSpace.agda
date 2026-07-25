------------------------------------------------------------------------
-- Sub-premetric spaces along injections
------------------------------------------------------------------------
--
-- Pulling a premetric back along an injective map from a set gives a
-- premetric; separatedness is the only axiom that consumes injectivity.
-- The predicate subspace is the special case given by fst, and completeness
-- transfers whenever the ambient limit has a point in the relevant fiber.
--
-- Reference: H. Ishihara, "A constructive theory of uniform spaces and
-- its application to integration theory" (Verona, 2024), Lemma 11.
------------------------------------------------------------------------

module Cubical.Relation.Premetric.Instances.SubSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base using (fiber)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings

open PositiveRationals
open PremetricTheory

private
  variable
    ℓA ℓB ℓM ℓM' ℓ' : Level

isInjective : {A : Type ℓA} {B : Type ℓB} → (A → B) → Type (ℓ-max ℓA ℓB)
isInjective ι = ∀ x y → ι x ≡ ι y → x ≡ y

module SubSpace↪
  (M' : PremetricSpace ℓM ℓM')
  {A : Type ℓA} (is-set-A : isSet A)
  (ι : A → ⟨ M' ⟩) (ι-injective : isInjective ι)
  where
  private
    module M = PremetricStr (snd M')

  infix 5 _≈↪[_]_
  _≈↪[_]_ : A → ℚ₊ → A → Type ℓM'
  x ≈↪[ ε ] y = ι x M.≈[ ε ] ι y

  isPremetric↪ : IsPremetric _≈↪[_]_
  isPremetric↪ .IsPremetric.isSetM        = is-set-A
  isPremetric↪ .IsPremetric.isProp≈       = λ _ _ _     → M.isProp≈ _ _ _
  isPremetric↪ .IsPremetric.isRefl≈       = λ _ _       → M.isRefl≈ _ _
  isPremetric↪ .IsPremetric.isSym≈        = λ _ _ _     → M.isSym≈ _ _ _
  isPremetric↪ .IsPremetric.isSeparated≈  =
    λ x y x≈y → ι-injective x y (M.isSeparated≈ _ _ x≈y)
  isPremetric↪ .IsPremetric.isTriangular≈ = λ _ _ _ _ _ → M.isTriangular≈ _ _ _ _ _
  isPremetric↪ .IsPremetric.isRounded≈    = λ _ _ _     → M.isRounded≈ _ _ _

  ↪PremetricSpace : PremetricSpace ℓA ℓM'
  fst ↪PremetricSpace = A
  PremetricStr._≈[_]_      (snd ↪PremetricSpace) = _≈↪[_]_
  PremetricStr.isPremetric (snd ↪PremetricSpace) = isPremetric↪

  ι↪ⁿ : NE[ ↪PremetricSpace , M' ]
  fst ι↪ⁿ = ι
  IsNonExpansive.pres≈ (snd ι↪ⁿ) = λ _ _ _ → idfun _

  ι↪ᶜ : C[ ↪PremetricSpace , M' ]
  ι↪ᶜ = NE→C ι↪ⁿ

  ι↪ᵘᶜ : UC[ ↪PremetricSpace , M' ]
  ι↪ᵘᶜ = NE→UC ι↪ⁿ

  ι↪ᴸ : L[ ↪PremetricSpace , M' ]
  ι↪ᴸ = NE→L ι↪ⁿ

  module _ (M-com : isComplete M') where
    lim↪→isComplete
      : (∀ x xs → fiber ι (fst (M-com (ι ∘ x) xs)))
      → isComplete ↪PremetricSpace
    lim↪→isComplete lim↪ x xs .fst = fst (lim↪ x xs)
    lim↪→isComplete lim↪ x xs .snd ε θ =
      subst≈R M' (sym (snd (lim↪ x xs)))
        (snd (M-com (ι ∘ x) xs) ε θ)

module SubSpace
  (M' : PremetricSpace ℓM ℓM')
  (P : ⟨ M' ⟩ → Type ℓ') (is-prop-valued : ∀ x → isProp (P x))
  where
  private
    M = ⟨ M' ⟩
    module M = PremetricStr (snd M')
    Carrier = Σ[ m ∈ M ] P m

    fst-injective : isInjective (fst {B = P})
    fst-injective x y = Σ≡Prop is-prop-valued

    module S = SubSpace↪ M'
      (isSetΣSndProp M.isSetM is-prop-valued)
      (fst {B = P}) fst-injective

  infix 5 _≈⊆[_]_
  _≈⊆[_]_ : Carrier → ℚ₊ → Carrier → Type ℓM'
  _≈⊆[_]_ = S._≈↪[_]_

  isPremetric⊆ : IsPremetric _≈⊆[_]_
  isPremetric⊆ = S.isPremetric↪

  ⊆PremetricSpace : PremetricSpace (ℓ-max ℓM ℓ') ℓM'
  ⊆PremetricSpace = S.↪PremetricSpace

  ι⊆ⁿ : NE[ ⊆PremetricSpace , M' ]
  ι⊆ⁿ = S.ι↪ⁿ

  ι⊆ᶜ : C[ ⊆PremetricSpace , M' ]
  ι⊆ᶜ = S.ι↪ᶜ

  ι⊆ᵘᶜ : UC[ ⊆PremetricSpace , M' ]
  ι⊆ᵘᶜ = S.ι↪ᵘᶜ

  ι⊆ᴸ : L[ ⊆PremetricSpace , M' ]
  ι⊆ᴸ = S.ι↪ᴸ

  module _ (M-com : isComplete M') where
    lim∈→isComplete : (∀ x xs → P (fst (M-com (fst ∘ x) xs))) → isComplete ⊆PremetricSpace
    lim∈→isComplete lim∈ = S.lim↪→isComplete M-com
      λ x xs → (fst (M-com (fst ∘ x) xs) , lim∈ x xs) , refl
