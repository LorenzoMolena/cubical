{-
  Binary products of premetric spaces

  `(x , y) ≈×[ ε ] (x' , y')` is componentwise closeness at the same ε,
  i.e. the max (Chebyshev) premetric without ever forming a max.  The
  projections are non-expanding, and pairing `⟨ f , g ⟩` preserves each
  mapping class: non-expanding, continuous, uniformly continuous
  (pointwise `min₊` of the two moduli) and Lipschitz (constant
  `max₊ L R`).

  Reference: H. Ishihara, "A constructive theory of uniform spaces and
  its application to integration theory" (Verona, 2024), Lemma 31 and
  Proposition 32.

-}

module Cubical.Relation.Premetric.Instances.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP using (⟨_⟩ ; str)

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (≡-×)

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.OrderedCommRing
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

module _ {ℓM ℓM' ℓN ℓN'}
  (M : PremetricSpace ℓM ℓM')
  (N : PremetricSpace ℓN ℓN') where
  private
    module PM where
      open PremetricStr (snd M) public
      open PremetricTheory M public
    module PN where
      open PremetricStr (snd N) public
      open PremetricTheory N public

  infix 5 _≈×[_]_

  _≈×[_]_ : (⟨ M ⟩ × ⟨ N ⟩) → ℚ₊ → (⟨ M ⟩ × ⟨ N ⟩) → Type (ℓ-max ℓM' ℓN')
  (x , y) ≈×[ ε ] (x' , y') = x PM.≈[ ε ] x' × y PN.≈[ ε ] y'

  open IsPremetric
  isPremetric× : IsPremetric _≈×[_]_
  isPremetric× .isSetM = isSet× PM.isSetM PN.isSetM
  isPremetric× .isProp≈ x y ε     = isProp× (PM.isProp≈ _ _ ε) (PN.isProp≈ _ _ ε)
  isPremetric× .isRefl≈ x ε       = PM.isRefl≈ _ ε , PN.isRefl≈ _ ε
  isPremetric× .isSym≈  x y ε x≈y = PM.isSym≈ _ _ ε (fst x≈y) , PN.isSym≈ _ _ ε (snd x≈y)
  isPremetric× .isSeparated≈ x y xy≈ =
    ≡-× (PM.isSeparated≈ _ _ (fst ∘ xy≈)) (PN.isSeparated≈ _ _ (snd ∘ xy≈))
  isPremetric× .isTriangular≈ x y z ε δ x≈y y≈z =
      (PM.isTriangular≈ _ _ _ ε δ (fst x≈y) (fst y≈z))
    , (PN.isTriangular≈ _ _ _ ε δ (snd x≈y) (snd y≈z))
  isPremetric× .isRounded≈ x y ε x≈y = do
    (δM , δM<ε , x≈δx') ← PM.isRounded≈ _ _ ε (fst x≈y)
    (δN , δN<ε , y≈δy') ← PN.isRounded≈ _ _ ε (snd x≈y)
    return
      ( max₊ δM δN
      , max₊LUB< δM δN ε δM<ε δN<ε
      , PM.isMonotone≈≤ (L≤⊔ {b = ⟨ δN ⟩₊}) x≈δx'
      , PN.isMonotone≈≤ (R≤⊔ {a = ⟨ δM ⟩₊}) y≈δy')

open PremetricStr
_×PrSp_ : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN'
        → PremetricSpace (ℓ-max ℓM ℓN) (ℓ-max ℓM' ℓN')
fst (M ×PrSp N) = ⟨ M ⟩ × ⟨ N ⟩
_≈[_]_      (snd (M ×PrSp N)) = _≈×[_]_ M N
isPremetric (snd (M ×PrSp N)) = isPremetric× M N

module _ {ℓM ℓM' ℓN ℓN'}
  (M : PremetricSpace ℓM ℓM')
  (N : PremetricSpace ℓN ℓN') where
  private
    module PM where
      open PremetricStr (snd M) public
      open PremetricTheory M public
    module PN where
      open PremetricStr (snd N) public
      open PremetricTheory N public

  projⁿ₁ : NE[ M ×PrSp N , M ]
  fst projⁿ₁ = fst
  IsNonExpansive.pres≈ (snd projⁿ₁) _ _ _ = fst

  projⁿ₂ : NE[ M ×PrSp N , N ]
  fst projⁿ₂ = snd
  IsNonExpansive.pres≈ (snd projⁿ₂) _ _ _ = snd

  projᶜ₁ : C[ M ×PrSp N , M ]
  projᶜ₁ = NE→C projⁿ₁

  projᶜ₂ : C[ M ×PrSp N , N ]
  projᶜ₂ = NE→C projⁿ₂

  projᵘᶜ₁ : UC[ M ×PrSp N , M ]
  projᵘᶜ₁ = NE→UC projⁿ₁

  projᵘᶜ₂ : UC[ M ×PrSp N , N ]
  projᵘᶜ₂ = NE→UC projⁿ₂

  projᴸ₁ : L[ M ×PrSp N , M ]
  projᴸ₁ = NE→L projⁿ₁

  projᴸ₂ : L[ M ×PrSp N , N ]
  projᴸ₂ = NE→L projⁿ₂

  module _ {ℓK ℓK'} {K : PremetricSpace ℓK ℓK'} where
    private
      module PK where
        open PremetricStr (snd K) public
        open PremetricTheory K public

    ⟨_,_⟩ⁿ : NE[ K , M ] → NE[ K , N ] → NE[ K , M ×PrSp N ]
    fst (fst ⟨ f , g ⟩ⁿ x) = fst f x
    snd (fst ⟨ f , g ⟩ⁿ x) = fst g x
    fst (pres≈ (snd ⟨ f , g ⟩ⁿ) x y ε x≈y) = pres≈ (snd f) x y ε x≈y
    snd (pres≈ (snd ⟨ f , g ⟩ⁿ) x y ε x≈y) = pres≈ (snd g) x y ε x≈y

    ⟨_,_⟩ᶜ : C[ K , M ] → C[ K , N ] → C[ K , M ×PrSp N ]
    fst ⟨ f , g ⟩ᶜ = λ x → fst f x , fst g x
    pres≈ (snd ⟨ f , g ⟩ᶜ x) ε = do
      (δM , fδ) ← pres≈ (snd f x) ε
      (δN , gδ) ← pres≈ (snd g x) ε
      return
        ( min₊ δM δN
        , λ y x≈y →
          ( fδ y (PK.isMonotone≈≤ (min₊≤L δM δN) x≈y)
          , gδ y (PK.isMonotone≈≤ (min₊≤R δM δN) x≈y)))

    ⟨_,_⟩ᵘᶜ : UC[ K , M ] → UC[ K , N ] → UC[ K , M ×PrSp N ]
    fst ⟨ f , g ⟩ᵘᶜ = λ x → fst f x , fst g x
    pres≈ (snd ⟨ f , g ⟩ᵘᶜ) ε = do
      (δM , fδ) ← pres≈ (snd f) ε
      (δN , gδ) ← pres≈ (snd g) ε
      return
        ( min₊ δM δN
        , λ x y x≈y →
          ( fδ x y (PK.isMonotone≈≤ (min₊≤L δM δN) x≈y)
          , gδ x y (PK.isMonotone≈≤ (min₊≤R δM δN) x≈y)))

    ⟨_,_⟩ᴸ : L[ K , M ] → L[ K , N ] → L[ K , M ×PrSp N ]
    fst ⟨ f , g ⟩ᴸ = λ x → fst f x , fst g x
    snd ⟨ f , g ⟩ᴸ = do
      (L , L-lip) ← snd f
      (R , R-lip) ← snd g
      return
        ( max₊ L R
        , islipschitzwith λ x y ε x≈y →
          ( PM.isMonotone≈≤
            (L≤⊔ {a = ⟨ L ⟩₊} {b = ⟨ R ⟩₊} ≤·[ fst ε , <-≤-weaken _ _ (snd ε) ])
            (pres≈ L-lip x y ε x≈y)
          , PN.isMonotone≈≤
            (R≤⊔ {a = ⟨ L ⟩₊} {b = ⟨ R ⟩₊} ≤·[ fst ε , <-≤-weaken _ _ (snd ε) ])
            (R-lip .pres≈ x y ε x≈y)))

-- examples with ℚ:
private
  open import Cubical.Relation.Premetric.Instances.Rationals using (ℚPremetricSpace)

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
