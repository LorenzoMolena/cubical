module Cubical.Relation.Premetric.Instances.Scaled where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings

open PositiveRationals
open ℚ₊Inverse

private
  variable
    ℓM ℓM' ℓN ℓN' : Level

module Scaled (M : PremetricSpace ℓM ℓM') (L : ℚ₊) where
  private
    module M where
      open PremetricStr (snd M) public
      open PremetricTheory M public

  infix 5 _≈[·_]_

  _≈[·_]_ : ⟨ M ⟩ → ℚ₊ → ⟨ M ⟩ → Type ℓM'
  x ≈[· ε ] y = x M.≈[ L ·₊ ε ] y

  isPremetricScaled : IsPremetric _≈[·_]_
  isPremetricScaled .IsPremetric.isSetM        = M.isSetM
  isPremetricScaled .IsPremetric.isProp≈       = λ _ _ _ → M.isProp≈ _ _ _
  isPremetricScaled .IsPremetric.isRefl≈       = λ _ _   → M.isRefl≈ _ _
  isPremetricScaled .IsPremetric.isSym≈        = λ _ _ _ → M.isSym≈ _ _ _
  isPremetricScaled .IsPremetric.isSeparated≈  = λ _ _ ≈L· →
    M.isSeparated≈ _ _ λ ε → M.subst≈ _ _ (·/ L ε) (≈L· (ε / L))
  isPremetricScaled .IsPremetric.isTriangular≈ = λ _ _ _ _ _ →
    (M.subst≈ _ _ (sym (ℚ.·DistL+ ⟨ L ⟩₊ _ _)) ∘_) ∘ M.isTriangular≈ _ _ _ _ _
  isPremetricScaled .IsPremetric.isRounded≈    = λ x y ε → PT.map
    (λ (δ , δ<Lε , ≈δ) → (δ / L , <·→/< δ L ε δ<Lε , M.subst≈ _ _ (sym (·/ L δ)) ≈δ))
    ∘ M.isRounded≈ x y (L ·₊ ε)

  ·PremetricSpace : PremetricSpace ℓM ℓM'
  fst ·PremetricSpace = ⟨ M ⟩
  PremetricStr._≈[_]_      (snd ·PremetricSpace) = _≈[·_]_
  PremetricStr.isPremetric (snd ·PremetricSpace) = isPremetricScaled

  private
    module L·M = PremetricTheory ·PremetricSpace

  ·isCauchy→isCauchy/ : ∀ x → L·M.isCauchy x → M.isCauchy (x ∘ (_/ L))
  ·isCauchy→isCauchy/ x xc ε δ = M.subst≈ _ _
    (cong (⟨ L ⟩₊ ℚ.·_) (sym (ℚ.·DistR+ ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟨ L ⁻¹₊ ⟩₊)) ∙ ·/ L (ε +₊ δ))
    (xc (ε / L) (δ / L))

  isComplete· : M.isComplete → L·M.isComplete
  isComplete· Mcomp x xc .fst = fst (Mcomp _ (·isCauchy→isCauchy/ x xc))
  isComplete· Mcomp x xc .snd = λ ε θ →
    subst2 (M._≈[_] fst (Mcomp _ (·isCauchy→isCauchy/ x xc)))
      (cong x (ℚ₊≡ (sym (ℚ.·Assoc ⟨ L ⟩₊ _ _) ∙ ·/ L ε)))
      (ℚ₊≡ (sym (ℚ.·DistL+ ⟨ L ⟩₊ _ _)))
      (snd (Mcomp _ (·isCauchy→isCauchy/ x xc)) (L ·₊ ε) (L ·₊ θ))

module _ (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') (L : ℚ₊) where
  open Scaled N L renaming (·PremetricSpace to L·N)
  open IsNonExpansive
  open IsLipschitzWith

  L[,]≅NE[,·] : Iso (Σ[ f ∈ _ ] IsLipschitzWith (snd M) f (snd N) L) NE[ M , L·N ]
  L[,]≅NE[,·] .Iso.fun f .fst = fst f
  L[,]≅NE[,·] .Iso.fun f .snd .pres≈ = IsLipschitzWith.pres≈ (snd f)
  L[,]≅NE[,·] .Iso.inv f .fst = fst f
  L[,]≅NE[,·] .Iso.inv f .snd .pres≈ = IsNonExpansive.pres≈ (snd f)
  L[,]≅NE[,·] .Iso.sec f = NE≡ refl
  L[,]≅NE[,·] .Iso.ret f = Σ≡Prop (λ h → isPropIsLipschitzWith _ h _ L) refl

  L[,]≃NE[,·] : (Σ[ f ∈ _ ] IsLipschitzWith (snd M) f (snd N) L) ≃ NE[ M , L·N ]
  L[,]≃NE[,·] = isoToEquiv L[,]≅NE[,·]
