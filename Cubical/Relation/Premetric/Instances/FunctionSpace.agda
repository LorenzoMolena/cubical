module Cubical.Relation.Premetric.Instances.FunctionSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Properties as ℚ using ()

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Instances.SubSpace
open import Cubical.Relation.Premetric.Mappings

open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

private
  variable
    ℓA ℓM ℓM' ℓN ℓN' : Level

module FunctionSpace (A : Type ℓA) (N' : PremetricSpace ℓN ℓN') where
  private
    N = ⟨ N' ⟩
    module N where
      open PremetricStr (snd N') public
      open PremetricTheory N' public

  infix 5 _≈→[_]_

  -- Definition 2.14
  _≈→[_]_ : (A → N) → ℚ₊ → (A → N) → Type (ℓ-max ℓA ℓN')
  f ≈→[ ε ] g = ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (∀ x → f x N.≈[ δ ] g x)

  -- Lemma 2.15
  ≈→→pointwise : ∀ f g ε → f ≈→[ ε ] g → ∀ x → f x N.≈[ ε ] g x
  ≈→→pointwise f g ε =
    PT.rec (isPropΠ λ x → N.isProp≈ (f x) (g x) ε)
    λ (δ , δ<ε , pw) x → N.isMonotone≈< δ<ε (pw x)

  -- Theorem 2.16 (first part)
  isPremetric→ : IsPremetric _≈→[_]_
  isPremetric→ .IsPremetric.isSetM = isSet→ N.isSetM
  isPremetric→ .IsPremetric.isProp≈ _ _ _ = squash₁
  isPremetric→ .IsPremetric.isRefl≈ f ε =
    ∣ ε /2₊ , /2₊<id ε , (λ x → N.isRefl≈ (f x) (ε /2₊)) ∣₁
  isPremetric→ .IsPremetric.isSym≈ f g ε =
    PT.map λ (δ , δ<ε , pw) → (δ , δ<ε , λ x → N.isSym≈ (f x) (g x) δ (pw x))
  isPremetric→ .IsPremetric.isSeparated≈ f g f≈g =
    funExt λ x → N.isSeparated≈ (f x) (g x) λ ε → ≈→→pointwise f g ε (f≈g ε) x
  isPremetric→ .IsPremetric.isTriangular≈ f g h ε θ f≈g g≈h = do
    (δ₁ , δ₁<ε , fg) ← f≈g
    (δ₂ , δ₂<θ , gh) ← g≈h
    return
      ( δ₁ +₊ δ₂
      , +Mono< _ _ _ _ δ₁<ε δ₂<θ
      , λ x → N.isTriangular≈ _ _ _ _ _ (fg x) (gh x))
  isPremetric→ .IsPremetric.isRounded≈ f g ε f≈g = do
    (δ , δ<ε , pw) ← f≈g
    return
      (  mean₊ δ ε
      , <→mean< ⟨ δ ⟩₊ ⟨ ε ⟩₊ δ<ε
      , ∣ δ , <→<mean ⟨ δ ⟩₊ ⟨ ε ⟩₊ δ<ε , pw ∣₁)

  →PremetricSpace : PremetricSpace (ℓ-max ℓA ℓN) (ℓ-max ℓA ℓN')
  fst →PremetricSpace = A → N
  PremetricStr._≈[_]_      (snd →PremetricSpace) = _≈→[_]_
  PremetricStr.isPremetric (snd →PremetricSpace) = isPremetric→

  private module A→N = PremetricTheory →PremetricSpace

  isCauchy→isPointwiseCauchy : ∀ s → A→N.isCauchy s → ∀ x → N.isCauchy (λ ε → s ε x)
  isCauchy→isPointwiseCauchy s sc x ε δ = ≈→→pointwise (s ε) (s δ) (ε +₊ δ) (sc ε δ) x

  -- Theorem 2.16 (second part)
  isComplete→ : N.isComplete → A→N.isComplete
  isComplete→ Ncomp s sc .fst x   = fst (Ncomp _ (isCauchy→isPointwiseCauchy s sc x))
  isComplete→ Ncomp s sc .snd ε θ = return
    ( ε +₊ θ /2₊
    , +MonoL< _ _ ⟨ ε ⟩₊ (/2₊<id θ)
    , λ x → snd (Ncomp _ (isCauchy→isPointwiseCauchy s sc x)) ε (θ /2₊))

module _ (M' : PremetricSpace ℓM ℓM') (N' : PremetricSpace ℓN ℓN') where
  private
    M   = ⟨ M' ⟩
    N   = ⟨ N' ⟩

    module M = PremetricStr (snd M')

    module N where
      open PremetricStr (snd N') public
      open PremetricTheory N' public

    module M→N where
      open FunctionSpace M N' public
      open PremetricTheory →PremetricSpace public

  NE[_,_]PrSpace : PremetricSpace (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN') (ℓ-max ℓM ℓN')
  NE[_,_]PrSpace =
    SubSpace.⊆PremetricSpace M→N.→PremetricSpace
    (λ f → IsNonExpansive (snd M') f (snd N'))
    (λ f → isPropIsNonExpansive (snd M') f (snd N'))

  C[_,_]PrSpace : PremetricSpace (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN') (ℓ-max ℓM ℓN')
  C[_,_]PrSpace =
    SubSpace.⊆PremetricSpace M→N.→PremetricSpace
    (λ f → isContinuous (snd M') f (snd N'))
    (λ f → isPropIsContinuous (snd M') f (snd N'))

  UC[_,_]PrSpace : PremetricSpace (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN') (ℓ-max ℓM ℓN')
  UC[_,_]PrSpace =
    SubSpace.⊆PremetricSpace M→N.→PremetricSpace
    (λ f → IsUContinuous (snd M') f (snd N'))
    (λ f → isPropIsUContinuous (snd M') f (snd N'))

  L[_,_]PrSpace : PremetricSpace (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN') (ℓ-max ℓM ℓN')
  L[_,_]PrSpace =
    SubSpace.⊆PremetricSpace M→N.→PremetricSpace
    (λ f → isLipschitz (snd M') f (snd N'))
    (λ f → isPropIsLipschitz (snd M') f (snd N'))

  module EquiLipschitz where

    isEquiLipschitzWith : (ℚ₊ → M → N) → ℚ₊ → Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
    isEquiLipschitzWith s L = ∀ ε → IsLipschitzWith (snd M') (s ε) (snd N') L

    isEquiLipschitz : (ℚ₊ → M → N) → Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
    isEquiLipschitz s = ∃[ L ∈ ℚ₊ ] isEquiLipschitzWith s L

    EquiL[_,_] : Type (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN')
    EquiL[_,_] = Σ[ s ∈ (ℚ₊ → M → N) ] isEquiLipschitz s

    -- Lemma 2.17
    limEquiLipschitzWith : (Ncomp : N.isComplete)
      → ∀ s sc L
      → isEquiLipschitzWith s L
      → IsLipschitzWith (snd M') (fst (M→N.isComplete→ Ncomp s sc)) (snd N') L
    IsLipschitzWith.pres≈ (limEquiLipschitzWith Ncomp s sc L L-lip) x y ε x≈y =
      let
        l , l-lim = M→N.isComplete→ Ncomp s sc
      in
        proof l x N.≈[ L ·₊ ε ] l y , N.isProp≈ (l x) (l y) (L ·₊ ε) by
      do
        δ , δ<ε , x≈[δ]y ← M.isRounded≈ x y ε x≈y
        let
          Δ = [ (L ·₊ ε) -₊ (L ·₊ δ) ]⟨ [ (fst L) , (snd L) ]·< δ<ε ⟩

          s⟶l : ∀ z → N.isLimit (λ ε → s ε z) (l z)
          s⟶l z ε θ = M→N.≈→→pointwise (s ε) l (ε +₊ θ) (l-lim ε θ) z

          Δ/2+Δ/2+Lδ≡Lε : ⟨ Δ /2₊ +₊ (Δ /2₊ +₊ L ·₊ δ) ⟩₊ ≡ ⟨ L ·₊ ε ⟩₊
          Δ/2+Δ/2+Lδ≡Lε =
            ⟨ Δ /2₊ +₊ (Δ /2₊ +₊ L ·₊ δ) ⟩₊ ≡⟨ ℚ.+Assoc ⟨ Δ /2₊ ⟩₊ _ _ ⟩
            ⟨ (Δ /2₊ +₊ Δ /2₊) +₊ L ·₊ δ ⟩₊ ≡⟨ cong (ℚ._+ _) (/2+/2≡id ⟨ Δ ⟩₊) ⟩
            ⟨ Δ +₊ L ·₊ δ ⟩₊                ≡⟨ minusPlus₊ (L ·₊ ε) (L ·₊ δ) ⟩
            ⟨ L ·₊ ε ⟩₊                     ∎

        return
          (N.subst≈ (l x) (l y) Δ/2+Δ/2+Lδ≡Lε
            (N.isLim≈+₂ _ _ (l x) (l y) (L ·₊ δ) (Δ /2₊) (Δ /2₊) (s⟶l x) (s⟶l y)
              (IsLipschitzWith.pres≈ (L-lip (Δ /2₊)) x y δ x≈[δ]y)))

    limEquiLipschitz : (Ncomp : N.isComplete)
      → ∀ s → (sc : M→N.isCauchy s)
      → isEquiLipschitz s
      → isLipschitz (snd M') (fst (M→N.isComplete→ Ncomp s sc)) (snd N')
    limEquiLipschitz Ncomp s sc = PT.map
      (uncurry λ L isELip → L , limEquiLipschitzWith Ncomp s sc L isELip)
