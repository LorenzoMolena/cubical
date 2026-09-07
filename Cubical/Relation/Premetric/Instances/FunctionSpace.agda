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
    ℓA ℓM ℓM' ℓN ℓN' ℓX ℓX' : Level

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

    module M where
      open PremetricStr (snd M') public
      open PremetricTheory M' public

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

  module _ (Ncomp : N.isComplete) where

    limNE : ∀ s sc → (∀ ε → IsNonExpansive (snd M') (s ε) (snd N'))
          → IsNonExpansive (snd M') (fst (M→N.isComplete→ Ncomp s sc)) (snd N')
    IsNonExpansive.pres≈ (limNE s sc s-ne) x y ε x≈y = let
        l , l-lim = M→N.isComplete→ Ncomp s sc
        s⟶l : ∀ z → N.isLimit (λ ε → s ε z) (l z)
        s⟶l z ε θ = M→N.≈→→pointwise (s ε) l (ε +₊ θ) (l-lim ε θ) z
      in
        proof l x N.≈[ ε ] l y , N.isProp≈ (l x) (l y) ε by
      do
        ((δ , Δ) , δ+Δ≡ε , x≈[δ]y) ← M.isRounded≈Gap ε x≈y
        let
          Δ/2+Δ/2+δ≡ε : ⟨ Δ /2₊ +₊ (Δ /2₊ +₊ δ) ⟩₊ ≡ ⟨ ε ⟩₊
          Δ/2+Δ/2+δ≡ε =
            ⟨ Δ /2₊ +₊ (Δ /2₊ +₊ δ) ⟩₊ ≡⟨ ℚ.+Assoc ⟨ Δ /2₊ ⟩₊ _ _ ⟩
            ⟨ (Δ /2₊ +₊ Δ /2₊) +₊ δ ⟩₊ ≡⟨ cong (ℚ._+ _) (/2+/2≡id ⟨ Δ ⟩₊) ⟩
            ⟨ Δ +₊ δ ⟩₊                ≡⟨ ℚ.+Comm ⟨ Δ ⟩₊ ⟨ δ ⟩₊ ∙ δ+Δ≡ε ⟩
            ⟨ ε ⟩₊                     ∎

        return (N.subst≈ _ _ Δ/2+Δ/2+δ≡ε
          (N.isLim≈+₂ _ _ (l x) (l y) δ (Δ /2₊) (Δ /2₊) (s⟶l x) (s⟶l y)
            (IsNonExpansive.pres≈ (s-ne (Δ /2₊)) x y δ x≈[δ]y)))

    isCompleteNE : PremetricTheory.isComplete NE[_,_]PrSpace
    isCompleteNE = SubSpace.lim∈→isComplete
      M→N.→PremetricSpace _ (λ f → isPropIsNonExpansive (snd M') f (snd N'))
      (M→N.isComplete→ Ncomp) λ x xs → limNE (fst ∘ x) xs (snd ∘ x)

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

-- easier way to construct a binary nonexpansive mapping
module _
  (M : PremetricSpace ℓM ℓM')
  (N : PremetricSpace ℓN ℓN')
  (X : PremetricSpace ℓX ℓX') where
  open IsNonExpansive
  open PremetricStr (snd M)

  private
    open module M→X = FunctionSpace ⟨ M ⟩ X
    open module N→X = FunctionSpace ⟨ N ⟩ X
    ℓM'' = ℓ-max ℓM ℓM'
    ℓN'' = ℓ-max ℓN ℓN'
    ℓX'' = ℓ-max ℓX ℓX'
    ℓNE2 = ℓ-max ℓM'' (ℓ-max ℓN'' ℓX'')

  record NE₂[_,_,_] : Type ℓNE2 where
    no-eta-equality
    field
      fun : ⟨ M ⟩ → ⟨ N ⟩ → ⟨ X ⟩
      lNE : ∀ y → IsNonExpansive (snd M) (flip fun y) (snd X)
      rNE : ∀ x → IsNonExpansive (snd N) (fun x)      (snd X)

    makeNE₂ : NE[ M , NE[ N , X ]PrSpace ]
    fst (fst makeNE₂ x) = fun x
    snd (fst makeNE₂ x) = rNE x
    pres≈ (snd makeNE₂) x y ε = PT.map pres≈L ∘ isRounded≈ x y ε where
      pres≈L : Σ ℚ₊ (λ _ → _ × _) → Σ ℚ₊ (λ _ → _ × _)
      pres≈L = map-snd (map-snd λ x≈y z → pres≈ (lNE z) x y _ x≈y)

  open NE₂[_,_,_]
  NE→NE₂ : NE[ M , NE[ N , X ]PrSpace ] → NE₂[_,_,_]
  fun (NE→NE₂ f) = fst ∘ (fst f)
  pres≈ (lNE (NE→NE₂ f) y) a b ε = flip (N→X.≈→→pointwise _ _ ε) y ∘ pres≈ (snd f) a b ε
  rNE (NE→NE₂ f) x = snd (fst f x)

flipNE : {M : PremetricSpace ℓM ℓM'}
         {N : PremetricSpace ℓN ℓN'}
         {X : PremetricSpace ℓX ℓX'}
       → NE[ M , NE[ N , X ]PrSpace ] → NE[ N , NE[ M , X ]PrSpace ]
flipNE f = NE₂[_,_,_].makeNE₂ flipNE₂ module flipⁿ where
  open NE₂[_,_,_]
  flipNE₂ : NE₂[ _ , _ , _ ]
  flipNE₂ .fun = flip (fst ∘ (fst f))
  flipNE₂ .lNE = rNE (NE→NE₂ _ _ _ f)
  flipNE₂ .rNE = lNE (NE→NE₂ _ _ _ f)

evalⁿ : {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'}
      → NE[ M , NE[ NE[ M , N ]PrSpace , N ]PrSpace ]
evalⁿ = flipNE idⁿ

module ∘Properties (X' : PremetricSpace ℓX ℓX') where
  module _ {M' : PremetricSpace ℓM ℓM'} {N' : PremetricSpace ℓN ℓN'} where

    open IsNonExpansive
    open IsLipschitzWith
    open IsContinuousAt
    open IsUContinuous

    -- pre-composition of any kind of mappings is nonexpansive :

    -∘ⁿ_ : NE[ M' , N' ] → NE[ NE[ N' , X' ]PrSpace , NE[ M' , X' ]PrSpace ]
    fst (-∘ⁿ f)         = _∘NE f
    pres≈ (snd (-∘ⁿ f)) = λ _ _ _ → PT.map (map-snd (map-snd (_∘ fst f)))

    -∘ᴸ_ : L[ M' , N' ] → NE[ L[ N' , X' ]PrSpace , L[ M' , X' ]PrSpace ]
    fst (-∘ᴸ f)         = _∘L f
    pres≈ (snd (-∘ᴸ f)) = λ _ _ _ → PT.map (map-snd (map-snd (_∘ fst f)))

    -∘ᵘᶜ_ : UC[ M' , N' ] → NE[ UC[ N' , X' ]PrSpace , UC[ M' , X' ]PrSpace ]
    fst (-∘ᵘᶜ f)         = _∘UC f
    pres≈ (snd (-∘ᵘᶜ f)) = λ _ _ _ → PT.map (map-snd (map-snd (_∘ fst f)))

    -∘ᶜ_ : C[ M' , N' ] → NE[ C[ N' , X' ]PrSpace , C[ M' , X' ]PrSpace ]
    fst (-∘ᶜ f)         = _∘C f
    pres≈ (snd (-∘ᶜ f)) = λ _ _ _ → PT.map (map-snd (map-snd (_∘ fst f)))

    -- post-composition with a nonexpansive mappings is nonexpansive :

    _ⁿ∘ⁿ- : NE[ M' , N' ] → NE[ NE[ X' , M' ]PrSpace , NE[ X' , N' ]PrSpace ]
    fst (f ⁿ∘ⁿ-)         = f ∘NE_
    pres≈ (snd (f ⁿ∘ⁿ-)) = λ _ _ _ → PT.map (map-snd (map-snd (pres≈ (snd f) _ _ _ ∘_)))

    _ⁿ∘ᴸ- : NE[ M' , N' ] → NE[ L[ X' , M' ]PrSpace , L[ X' , N' ]PrSpace ]
    fst (f ⁿ∘ᴸ-)         = (NE→L f) ∘L_
    pres≈ (snd (f ⁿ∘ᴸ-)) = λ _ _ _ → PT.map (map-snd (map-snd (pres≈ (snd f) _ _ _ ∘_)))

    _ⁿ∘ᵘᶜ- : NE[ M' , N' ] → NE[ UC[ X' , M' ]PrSpace , UC[ X' , N' ]PrSpace ]
    fst (f ⁿ∘ᵘᶜ-)         = (NE→UC f) ∘UC_
    pres≈ (snd (f ⁿ∘ᵘᶜ-)) = λ _ _ _ → PT.map (map-snd (map-snd (pres≈ (snd f) _ _ _ ∘_)))

    _ⁿ∘ᶜ- : NE[ M' , N' ] → NE[ C[ X' , M' ]PrSpace , C[ X' , N' ]PrSpace ]
    fst (f ⁿ∘ᶜ-)         = (NE→C f) ∘C_
    pres≈ (snd (f ⁿ∘ᶜ-)) = λ _ _ _ → PT.map (map-snd (map-snd (pres≈ (snd f) _ _ _ ∘_)))
