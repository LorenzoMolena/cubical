------------------------------------------------------------------------
-- Binary products of premetric spaces
------------------------------------------------------------------------
--
-- `(x , y) ≈×[ ε ] (x' , y')` is componentwise closeness at the same ε,
-- i.e. the max (Chebyshev) premetric without ever forming a max.  The
-- projections are non-expanding, and pairing `⟨ f , g ⟩` preserves each
-- mapping class: non-expanding, continuous, uniformly continuous
-- (pointwise `min₊` of the two moduli) and Lipschitz (constant
-- `max₊ L R`).
--
-- Reference: H. Ishihara, "A constructive theory of uniform spaces and
-- its application to integration theory" (Verona, 2024), Lemma 31 and
-- Proposition 32.
------------------------------------------------------------------------

module Cubical.Relation.Premetric.Instances.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP using (⟨_⟩ ; str)

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (≡-×)

import Cubical.Data.Rationals.Properties as ℚProp
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open IsContinuousAt
open IsUContinuous
open IsLipschitzWith
open IsNonExpansive

open OrderedCommRingStr (str ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing
open PositiveRationals

private
  variable
    ℓK ℓK' ℓM ℓM' ℓN ℓN' : Level

-- Pure ℚ₊ bookkeeping for the max modulus/constant, independent of the
-- premetric spaces.
private
  max₊below : ∀ ε δ η → δ <₊ ε → η <₊ ε → max₊ δ η <₊ ε
  max₊below ε δ η δ<ε η<ε with ⟨ δ ⟩₊ ℚ.≟ ⟨ η ⟩₊
  ... | lt δ<η = subst (λ q → q ℚ.< ⟨ ε ⟩₊)
    (sym (ℚ.≤→max ⟨ δ ⟩₊ ⟨ η ⟩₊ (ℚ.<Weaken≤ _ _ δ<η)))
    η<ε
  ... | eq δ≡η = subst (λ q → q ℚ.< ⟨ ε ⟩₊)
    (sym (ℚ.≤→max ⟨ δ ⟩₊ ⟨ η ⟩₊ (ℚ.≡Weaken≤ _ _ δ≡η)))
    η<ε
  ... | gt η<δ = subst (λ q → q ℚ.< ⟨ ε ⟩₊)
    (sym (ℚProp.maxComm ⟨ δ ⟩₊ ⟨ η ⟩₊
        ∙ ℚ.≤→max ⟨ η ⟩₊ ⟨ δ ⟩₊ (ℚ.<Weaken≤ _ _ η<δ)))
    δ<ε

  ≤max₊L : ∀ δ η → δ ≤₊ max₊ δ η
  ≤max₊L δ η = ℚ.≤max ⟨ δ ⟩₊ ⟨ η ⟩₊

  ≤max₊R : ∀ δ η → η ≤₊ max₊ δ η
  ≤max₊R δ η = subst (λ q → ⟨ η ⟩₊ ℚ.≤ q)
    (ℚProp.maxComm ⟨ η ⟩₊ ⟨ δ ⟩₊)
    (ℚ.≤max ⟨ η ⟩₊ ⟨ δ ⟩₊)

  ·₊≤max₊L : ∀ L R ε → L ·₊ ε ≤₊ max₊ L R ·₊ ε
  ·₊≤max₊L L R ε = ℚ.recompute≤ $
    ·MonoR≤ ⟨ L ⟩₊ ⟨ max₊ L R ⟩₊ ⟨ ε ⟩₊
      (ℚ.<Weaken≤ 0r _ (snd ε))
      (≤max₊L L R)

  ·₊≤max₊R : ∀ L R ε → R ·₊ ε ≤₊ max₊ L R ·₊ ε
  ·₊≤max₊R L R ε = ℚ.recompute≤ $
    ·MonoR≤ ⟨ R ⟩₊ ⟨ max₊ L R ⟩₊ ⟨ ε ⟩₊
      (ℚ.<Weaken≤ 0r _ (snd ε))
      (≤max₊R L R)

module _ {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where
  private
    M = ⟨ M' ⟩
    N = ⟨ N' ⟩
    module PM where
      open PremetricStr (snd M') public
      open PremetricTheory M' public
    module PN where
      open PremetricStr (snd N') public
      open PremetricTheory N' public

  infix 5 _≈×[_]_

  _≈×[_]_ : (M × N) → ℚ₊ → (M × N) → Type (ℓ-max ℓM' ℓN')
  (x , y) ≈×[ ε ] (x' , y') = x PM.≈[ ε ] x' × y PN.≈[ ε ] y'

  isPremetric× : IsPremetric _≈×[_]_
  isPremetric× .IsPremetric.isSetM = isSet× PM.isSetM PN.isSetM
  isPremetric× .IsPremetric.isProp≈ (x , y) (x' , y') ε =
    isProp× (PM.isProp≈ x x' ε) (PN.isProp≈ y y' ε)
  isPremetric× .IsPremetric.isRefl≈ (x , y) ε =
    PM.isRefl≈ x ε , PN.isRefl≈ y ε
  isPremetric× .IsPremetric.isSym≈ (x , y) (x' , y') ε (x≈x' , y≈y') =
    PM.isSym≈ x x' ε x≈x' , PN.isSym≈ y y' ε y≈y'
  isPremetric× .IsPremetric.isSeparated≈ (x , y) (x' , y') xy≈ =
    ≡-×
      (PM.isSeparated≈ x x' λ ε → fst (xy≈ ε))
      (PN.isSeparated≈ y y' λ ε → snd (xy≈ ε))
  isPremetric× .IsPremetric.isTriangular≈
    (x , y) (x' , y') (x'' , y'') ε δ (x≈x' , y≈y') (x'≈x'' , y'≈y'') =
      PM.isTriangular≈ x x' x'' ε δ x≈x' x'≈x''
    , PN.isTriangular≈ y y' y'' ε δ y≈y' y'≈y''
  isPremetric× .IsPremetric.isRounded≈
    (x , y) (x' , y') ε (x≈x' , y≈y') = do
      (δM , δM<ε , x≈δx') ← PM.isRounded≈ x x' ε x≈x'
      (δN , δN<ε , y≈δy') ← PN.isRounded≈ y y' ε y≈y'
      return
        ( max₊ δM δN
        , max₊below ε δM δN δM<ε δN<ε
        , ( PM.isMonotone≈≤ (≤max₊L δM δN) x≈δx'
          , PN.isMonotone≈≤ (≤max₊R δM δN) y≈δy' ))

_×PrSp_ : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN'
       → PremetricSpace (ℓ-max ℓM ℓN) (ℓ-max ℓM' ℓN')
fst (M' ×PrSp N') = ⟨ M' ⟩ × ⟨ N' ⟩
snd (M' ×PrSp N') = premetricstr (_≈×[_]_ M' N') (isPremetric× M' N')

module _ {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where
  private
    module PM where
      open PremetricStr (snd M') public
      open PremetricTheory M' public
    module PN where
      open PremetricStr (snd N') public
      open PremetricTheory N' public

  projⁿ₁ : NE[ M' ×PrSp N' , M' ]
  fst projⁿ₁ = fst
  IsNonExpansive.pres≈ (snd projⁿ₁) _ _ _ = fst

  projⁿ₂ : NE[ M' ×PrSp N' , N' ]
  fst projⁿ₂ = snd
  IsNonExpansive.pres≈ (snd projⁿ₂) _ _ _ = snd

  projᶜ₁ : C[ M' ×PrSp N' , M' ]
  fst projᶜ₁ = fst
  snd projᶜ₁ = isNonExpansive→isContinuous _ fst _ (snd projⁿ₁)

  projᶜ₂ : C[ M' ×PrSp N' , N' ]
  fst projᶜ₂ = snd
  snd projᶜ₂ = isNonExpansive→isContinuous _ snd _ (snd projⁿ₂)

  projᵘᶜ₁ : UC[ M' ×PrSp N' , M' ]
  fst projᵘᶜ₁ = fst
  snd projᵘᶜ₁ = isNonExpansive→isUContinuous _ fst _ (snd projⁿ₁)

  projᵘᶜ₂ : UC[ M' ×PrSp N' , N' ]
  fst projᵘᶜ₂ = snd
  snd projᵘᶜ₂ = isNonExpansive→isUContinuous _ snd _ (snd projⁿ₂)

  projᴸ₁ : L[ M' ×PrSp N' , M' ]
  projᴸ₁ = NE→L projⁿ₁

  projᴸ₂ : L[ M' ×PrSp N' , N' ]
  projᴸ₂ = NE→L projⁿ₂

  module _ {ℓK ℓK'} {K : PremetricSpace ℓK ℓK'} where
    private
      module PK where
        open PremetricStr (snd K) public
        open PremetricTheory K public

    ⟨_,_⟩ⁿ : NE[ K , M' ] → NE[ K , N' ] → NE[ K , M' ×PrSp N' ]
    ⟨ f , g ⟩ⁿ =
      (λ x → fst f x , fst g x)
      , isnonexpansive λ x y ε x≈y →
          ( f .snd .pres≈ x y ε x≈y
          , g .snd .pres≈ x y ε x≈y )

    ⟨_,_⟩ᶜ : C[ K , M' ] → C[ K , N' ] → C[ K , M' ×PrSp N' ]
    ⟨ f , g ⟩ᶜ =
      (λ x → fst f x , fst g x)
      , λ x → iscontinuousat λ ε → do
          (δM , fδ) ← f .snd x .pres≈ ε
          (δN , gδ) ← g .snd x .pres≈ ε
          return
            ( min₊ δM δN
            , λ y x≈y →
                ( fδ y (PK.isMonotone≈≤ (min₊≤L δM δN) x≈y)
                , gδ y (PK.isMonotone≈≤ (min₊≤R δM δN) x≈y)))

    ⟨_,_⟩ᵘᶜ : UC[ K , M' ] → UC[ K , N' ] → UC[ K , M' ×PrSp N' ]
    ⟨ f , g ⟩ᵘᶜ =
      (λ x → fst f x , fst g x)
      , isucontinuous λ ε → do
          (δM , fδ) ← f .snd .pres≈ ε
          (δN , gδ) ← g .snd .pres≈ ε
          return
            ( min₊ δM δN
            , λ x y x≈y →
                ( fδ x y (PK.isMonotone≈≤ (min₊≤L δM δN) x≈y)
                , gδ x y (PK.isMonotone≈≤ (min₊≤R δM δN) x≈y)))

    ⟨_,_⟩ᴸ : L[ K , M' ] → L[ K , N' ] → L[ K , M' ×PrSp N' ]
    ⟨ f , g ⟩ᴸ =
      (λ x → fst f x , fst g x)
      , do
          (L , L-lip) ← f .snd
          (R , R-lip) ← g .snd
          return
            ( max₊ L R
            , islipschitzwith λ x y ε x≈y →
                ( PM.isMonotone≈≤
                    (·₊≤max₊L L R ε)
                    (L-lip .pres≈ x y ε x≈y)
                , PN.isMonotone≈≤
                    (·₊≤max₊R L R ε)
                    (R-lip .pres≈ x y ε x≈y) ))

open import Cubical.Relation.Premetric.Instances.Rationals using (ℚPremetricSpace)

private
  ℚ×PrSpℚ : PremetricSpace ℓ-zero ℓ-zero
  ℚ×PrSpℚ = ℚPremetricSpace ×PrSp ℚPremetricSpace

  projⁿ₁-ℚ : NE[ ℚ×PrSpℚ , ℚPremetricSpace ]
  projⁿ₁-ℚ = projⁿ₁ ℚPremetricSpace ℚPremetricSpace

  projⁿ₂-ℚ : NE[ ℚ×PrSpℚ , ℚPremetricSpace ]
  projⁿ₂-ℚ = projⁿ₂ ℚPremetricSpace ℚPremetricSpace

  pairⁿ-ℚ : NE[ ℚ×PrSpℚ , ℚ×PrSpℚ ]
  pairⁿ-ℚ = ⟨_,_⟩ⁿ ℚPremetricSpace ℚPremetricSpace projⁿ₁-ℚ projⁿ₂-ℚ

_ : projⁿ₁-ℚ ∘NE pairⁿ-ℚ ≡ projⁿ₁-ℚ
_ = NE≡ refl
