module Cubical.Relation.Premetric.Mappings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto hiding (id)
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Premetric

open PositiveRationals
open ℚ₊Inverse

private
  variable
    ℓ ℓ' ℓM ℓM' ℓN ℓN' ℓO ℓO' : Level

module _
  {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A)
  (f : A → B)
  (N : PremetricStr ℓN' B)
  where

  private
    module M where
      open PremetricStr M public
      open PremetricTheory (_ , M) public
    module N where
      open PremetricStr N public
      open PremetricTheory (_ , N) public

  record IsContinuousAt (x : A) : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor iscontinuousat
    field
      pres≈ : ∀ ε → ∃[ δ ∈ ℚ₊ ] (∀ y → x M.≈[ δ ] y → f x N.≈[ ε ] f y)

  unquoteDecl IsContinuousAtIsoΣ = declareRecordIsoΣ IsContinuousAtIsoΣ (quote IsContinuousAt)

  isPropIsContinuousAt : ∀ x → isProp (IsContinuousAt x)
  isPropIsContinuousAt x = isOfHLevelRetractFromIso 1
    IsContinuousAtIsoΣ $ isPropΠ λ _ → squash₁

  isContinuous : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isContinuous = ∀ x → IsContinuousAt x

  isPropIsContinuous : isProp isContinuous
  isPropIsContinuous = isPropΠ isPropIsContinuousAt

  record IsUContinuousWith (μ : ℚ₊ → ℚ₊) : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor isucontinuouswith
    field
      pres≈ : ∀ x y ε → x M.≈[ μ ε ] y → f x N.≈[ ε ] f y

  unquoteDecl IsUContinuousWithIsoΣ = declareRecordIsoΣ IsUContinuousWithIsoΣ (quote IsUContinuousWith)

  isPropIsUContinuousWith : ∀ μ → isProp (IsUContinuousWith μ)
  isPropIsUContinuousWith μ = isOfHLevelRetractFromIso 1
    IsUContinuousWithIsoΣ $ isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  record IsUContinuous : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor isucontinuous
    field
      pres≈ : ∀ ε → ∃[ μ ∈ ℚ₊ ] (∀ x y → x M.≈[ μ ] y → f x N.≈[ ε ] f y)

  unquoteDecl IsUContinuousIsoΣ = declareRecordIsoΣ IsUContinuousIsoΣ (quote IsUContinuous)

  isPropIsUContinuous : isProp IsUContinuous
  isPropIsUContinuous = isOfHLevelRetractFromIso 1
    IsUContinuousIsoΣ (isPropΠ λ _ → squash₁)

  ∃IsUContinuousWith→isUContinuous : ∃[ μ ∈ _ ] IsUContinuousWith μ → IsUContinuous
  IsUContinuous.pres≈ (∃IsUContinuousWith→isUContinuous is-uc) ε = do
    (μ , μ-uc) ← is-uc
    return λ where
      .fst     → μ ε
      .snd x y → μ-uc .IsUContinuousWith.pres≈ x y ε

  record IsLipschitzWith (L : ℚ₊) : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor islipschitzwith
    field
      pres≈ : ∀ x y ε → x M.≈[ ε ] y → f x N.≈[ L ·₊ ε ] f y

  unquoteDecl IsLipschitzWithIsoΣ = declareRecordIsoΣ IsLipschitzWithIsoΣ (quote IsLipschitzWith)

  isPropIsLipschitzWith : ∀ L → isProp (IsLipschitzWith L)
  isPropIsLipschitzWith L = isOfHLevelRetractFromIso 1
    IsLipschitzWithIsoΣ $ isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  isLipschitz : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isLipschitz = ∃[ L ∈ ℚ₊ ] IsLipschitzWith L

  isPropIsLipschitz : isProp isLipschitz
  isPropIsLipschitz = squash₁

  record IsNonExpansive : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor isnonexpansive
    field
      pres≈ : ∀ x y ε → x M.≈[ ε ] y → f x N.≈[ ε ] f y

  unquoteDecl IsNonExpansiveIsoΣ = declareRecordIsoΣ IsNonExpansiveIsoΣ (quote IsNonExpansive)

  isPropIsNonExpansive : isProp IsNonExpansive
  isPropIsNonExpansive = isOfHLevelRetractFromIso 1 IsNonExpansiveIsoΣ $
    isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  -- NonExpansive mappings are equivalent to Lipschitz mappings with constant 1:

  isNonExpansive→isLipschitzWith1 : IsNonExpansive → IsLipschitzWith 1
  IsLipschitzWith.pres≈ (isNonExpansive→isLipschitzWith1 is-ne) x y ε =
    N.subst≈ (f x) (f y) (sym (ℚ.·IdL ⟨ ε ⟩₊)) ∘ is-ne .IsNonExpansive.pres≈ x y ε

  isLipschitzWith1→isNonExpansive : IsLipschitzWith 1 → IsNonExpansive
  IsNonExpansive.pres≈ (isLipschitzWith1→isNonExpansive 1-lip) x y ε =
    N.subst≈ (f x) (f y) (ℚ.·IdL ⟨ ε ⟩₊) ∘ 1-lip .IsLipschitzWith.pres≈ x y ε

  IsNonExpansive≃IsLipschitzWith1 : IsNonExpansive ≃ IsLipschitzWith 1
  IsNonExpansive≃IsLipschitzWith1 = propBiimpl→Equiv
    isPropIsNonExpansive (isPropIsLipschitzWith 1)
    isNonExpansive→isLipschitzWith1 isLipschitzWith1→isNonExpansive

  -- Implications NonExpanding ⇒ Lipschitz ⇒ UContinuous ⇒ Continuous :

  isNonExpansive→isLipschitz : IsNonExpansive → isLipschitz
  isNonExpansive→isLipschitz is-ne = ∣ 1 , isNonExpansive→isLipschitzWith1 is-ne ∣₁

  isLipschitzWith→isUContinuousWith/ : ∀ L → IsLipschitzWith L → IsUContinuousWith (_/ L)
  IsUContinuousWith.pres≈ (isLipschitzWith→isUContinuousWith/ L L-lip) =
    λ x y ε → N.subst≈ (f x) (f y) (·/ L ε) ∘ L-lip .IsLipschitzWith.pres≈ x y (ε / L)

  isLipschitz→isUContinuous : isLipschitz → IsUContinuous
  isLipschitz→isUContinuous = PT.rec isPropIsUContinuous $
    ∃IsUContinuousWith→isUContinuous ∘ ∣_∣₁ ∘ uncurry λ L L-lip → λ where
      .fst → _/ L
      .snd → isLipschitzWith→isUContinuousWith/ L L-lip

  isUContinuousWith→isContinuous : ∀ μ → IsUContinuousWith μ → isContinuous
  IsContinuousAt.pres≈ (isUContinuousWith→isContinuous μ μ-uc x) ε =
    return λ where
      .fst   → μ ε
      .snd y → μ-uc .IsUContinuousWith.pres≈ x y ε

  isUContinuous→isContinuous : IsUContinuous → isContinuous
  IsContinuousAt.pres≈ (isUContinuous→isContinuous is-uc x) ε = do
    (δ , ≈δ→f≈ε) ← is-uc .IsUContinuous.pres≈ ε
    return λ where
      .fst → δ
      .snd → ≈δ→f≈ε x

  -- we prove this two implications directly, instead of passing through
  -- `isNonExpansive→isLipschitz` to avoid a " / 1" in the definition of μ
  isNonExpansive→isUContinuousWithId : IsNonExpansive → IsUContinuousWith (idfun ℚ₊)
  IsUContinuousWith.pres≈ (isNonExpansive→isUContinuousWithId is-ne) =
    IsNonExpansive.pres≈ is-ne

  isNonExpansive→isUContinuous : IsNonExpansive → IsUContinuous
  isNonExpansive→isUContinuous =
    curry (∃IsUContinuousWith→isUContinuous ∘ ∣_∣₁) _ ∘ isNonExpansive→isUContinuousWithId

  isLipschitz→isContinuous : isLipschitz → isContinuous
  isLipschitz→isContinuous = isUContinuous→isContinuous ∘ isLipschitz→isUContinuous

  isNonExpansive→isContinuous : IsNonExpansive → isContinuous
  isNonExpansive→isContinuous = isUContinuous→isContinuous ∘ isNonExpansive→isUContinuous

C[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
C[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] isContinuous (M .snd) f (N .snd)

UC[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
UC[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] IsUContinuous (M .snd) f (N .snd)

L[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
L[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] isLipschitz (M .snd) f (N .snd)

NE[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
NE[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] IsNonExpansive (M .snd) f (N .snd)

module _ {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} where

  NE→L : NE[ M , N ] → L[ M , N ]
  fst (NE→L f) = fst f
  snd (NE→L f) = isNonExpansive→isLipschitz _ (fst f) _ (snd f)

  NE→UC : NE[ M , N ] → UC[ M , N ]
  fst (NE→UC f) = fst f
  snd (NE→UC f) = isNonExpansive→isUContinuous _ (fst f) _ (snd f)

  L→UC : L[ M , N ] → UC[ M , N ]
  fst (L→UC f) = fst f
  snd (L→UC f) = isLipschitz→isUContinuous _ (fst f) _ (snd f)

  UC→C : UC[ M , N ] → C[ M , N ]
  fst (UC→C f) = fst f
  snd (UC→C f) = isUContinuous→isContinuous _ (fst f) _ (snd f)

  NE→C : NE[ M , N ] → C[ M , N ]
  NE→C = UC→C ∘ NE→UC

  L→C : L[ M , N ] → C[ M , N ]
  L→C = UC→C ∘ L→UC

-- The identity function is NonExpansive, Continuous, UContinuous and Lipschitz:
module _ {M : PremetricSpace ℓM ℓM'} where

  idⁿ : NE[ M , M ]
  fst idⁿ = idfun _
  IsNonExpansive.pres≈ (snd idⁿ) = λ _ _ _ → idfun _

  idᶜ : C[ M , M ]
  fst idᶜ = idfun _
  snd idᶜ = isNonExpansive→isContinuous _ _ _ (idⁿ .snd)

  idᵘᶜ : UC[ M , M ]
  fst idᵘᶜ = idfun _
  snd idᵘᶜ = isNonExpansive→isUContinuous _ _ _ (idⁿ .snd)

  idᴸ : L[ M , M ]
  fst idᴸ = idfun _
  snd idᴸ = isNonExpansive→isLipschitz _ _ _ (idⁿ .snd)

-- Composiontions of mappings:
module _
  {M : PremetricSpace ℓM ℓM'}
  {N : PremetricSpace ℓN ℓN'}
  {O : PremetricSpace ℓO ℓO'} where

  _∘NE_ : NE[ N , O ] → NE[ M , N ] → NE[ M , O ]
  fst (g ∘NE f) = fst g ∘ fst f
  IsNonExpansive.pres≈ (snd (g ∘NE f)) =
    λ x y ε → g .snd .pres≈ (fst f x) (fst f y) ε ∘ f .snd .pres≈ x y ε
    where open IsNonExpansive

  _∘C_ : C[ N , O ] → C[ M , N ] → C[ M , O ]
  fst (g ∘C f) = fst g ∘ fst f
  IsContinuousAt.pres≈ (snd (g ∘C f) x) = λ ε → do
    (δ , ≈δ→≈ε) ← g .snd (fst f x) .pres≈ ε
    (η , ≈η→≈δ) ← f .snd x .pres≈ δ
    return λ where
      .fst   → η
      .snd y → ≈δ→≈ε (fst f y) ∘ ≈η→≈δ y
    where open IsContinuousAt

  _∘UC_ : UC[ N , O ] → UC[ M , N ] → UC[ M , O ]
  fst (g ∘UC f) = fst g ∘ fst f
  IsUContinuous.pres≈ (snd (g ∘UC f)) ε = do
    (ν , ν-uc) ← g .snd .pres≈ ε
    (μ , μ-uc) ← f .snd .pres≈ ν
    return λ where
      .fst     → μ
      .snd x y → ν-uc (fst f x) (fst f y) ∘ μ-uc x y
    where open IsUContinuous

  _∘L_ : L[ N , O ] → L[ M , N ] → L[ M , O ]
  fst (g ∘L f) = fst g ∘ fst f
  snd (g ∘L f) = do
    (L , L-lip) ← f .snd
    (R , R-lip) ← g .snd
    return λ where
      .fst → R ·₊ L
      .snd .pres≈ x y ε →
        subst≈ (fst g (fst f x)) (fst g (fst f y)) (ℚ.·Assoc ⟨ R ⟩₊ ⟨ L ⟩₊ _)
        ∘ R-lip .pres≈ (fst f x) (fst f y) (L ·₊ ε)
        ∘ L-lip .pres≈ x y ε
    where
      open IsLipschitzWith
      open PremetricTheory O

C≡ : ∀ {M N : PremetricSpace ℓM ℓM'} → {f g : C[ M , N ]} → fst f ≡ fst g → f ≡ g
C≡ = ΣPathPProp (flip (isPropIsContinuous _) _)

UC≡ : ∀ {M N : PremetricSpace ℓM ℓM'} → {f g : UC[ M , N ]} → fst f ≡ fst g → f ≡ g
UC≡ = ΣPathPProp (flip (isPropIsUContinuous _) _)

L≡ : ∀ {M N : PremetricSpace ℓM ℓM'} → {f g : L[ M , N ]} → fst f ≡ fst g → f ≡ g
L≡ = ΣPathPProp λ _ → squash₁

NE≡ : ∀ {M N : PremetricSpace ℓM ℓM'} → {f g : NE[ M , N ]} → fst f ≡ fst g → f ≡ g
NE≡ = ΣPathPProp (flip (isPropIsNonExpansive _) _)

record IsIsometry {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A) (e : A ≃ B) (N : PremetricStr ℓN' B)
  : Type (ℓ-suc (ℓ-max ℓM (ℓ-max ℓN (ℓ-max ℓM' ℓN'))))
  where
  no-eta-equality
  constructor isisometry
  -- Shorter qualified names
  private
    module M = PremetricStr M
    module N = PremetricStr N

  field
    pres≈ : ∀ x ε y → x M.≈[ ε ] y ≃ equivFun e x N.≈[ ε ] equivFun e y

unquoteDecl IsIsometryIsoΣ = declareRecordIsoΣ IsIsometryIsoΣ (quote IsIsometry)

Isometry[_,_] : (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') → Type _
Isometry[ M , N ] = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsIsometry (M .snd) e (N .snd)

module _
  {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A) (e : A ≃ B) (N : PremetricStr ℓN' B) where

  private
    module M = PremetricStr M
    module N = PremetricStr N

  isPropIsIsometry : isProp (IsIsometry M e N)
  isPropIsIsometry = isOfHLevelRetractFromIso 1
    IsIsometryIsoΣ $ isPropΠ3 λ _ _ _ → isOfHLevel≃ 1
      (isProp≈ M _ _ _) (isProp≈ N _ _ _)
      where open PremetricStr

  isIsometry→invEquivIsIsometry : IsIsometry M e N → IsIsometry N (invEquiv e) M
  IsIsometry.pres≈ (isIsometry→invEquivIsIsometry ise) x ε y = invEquiv $
       pres≈ ise (invEq e x) ε (invEq e y)
    ∙ₑ pathToEquiv (cong₂ N._≈[ ε ]_ (secEq e x) (secEq e y))
    where open IsIsometry

  isIsometry→isNonExpansive : IsIsometry M e N → IsNonExpansive M (equivFun e) N
  IsNonExpansive.pres≈ (isIsometry→isNonExpansive ise) x y ε =
    equivFun (IsIsometry.pres≈ ise x ε y)

  isIsometry→isContinuous : IsIsometry M e N → isContinuous M (equivFun e) N
  isIsometry→isContinuous =
    isNonExpansive→isContinuous M (equivFun e) N ∘ isIsometry→isNonExpansive

  isIsometry→isUContinuous : IsIsometry M e N → IsUContinuous M (equivFun e) N
  isIsometry→isUContinuous =
    isNonExpansive→isUContinuous M (equivFun e) N ∘ isIsometry→isNonExpansive

  isIsometry→isLipschitz : IsIsometry M e N → isLipschitz M (equivFun e) N
  isIsometry→isLipschitz =
    isNonExpansive→isLipschitz M (equivFun e) N ∘ isIsometry→isNonExpansive

module _ {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} where

  invIsometry : Isometry[ M , N ] → Isometry[ N , M ]
  fst (invIsometry e) = invEquiv (fst e)
  snd (invIsometry e) = isIsometry→invEquivIsIsometry _ (fst e) _ (snd e)

  Isometry→NE : Isometry[ M , N ] → NE[ M , N ]
  fst (Isometry→NE e) = equivFun (fst e)
  snd (Isometry→NE e) = isIsometry→isNonExpansive _ (fst e) _ (snd e)

  Isometry→L : Isometry[ M , N ] → L[ M , N ]
  Isometry→L = NE→L ∘ Isometry→NE

  Isometry→UC : Isometry[ M , N ] → UC[ M , N ]
  Isometry→UC = NE→UC ∘ Isometry→NE

  Isometry→C : Isometry[ M , N ] → C[ M , N ]
  Isometry→C = NE→C ∘ Isometry→NE

module _ {ℓ ℓ' : Level} where
  𝒮ᴰ-Premetric : DUARel (𝒮-Univ ℓ) (PremetricStr ℓ') (ℓ-suc (ℓ-max ℓ ℓ'))
  𝒮ᴰ-Premetric =
    𝒮ᴰ-Record (𝒮-Univ _) IsIsometry
      (fields:
        data[ _≈[_]_ ∣ ternRel ∣ pres≈ ]
        prop[ isPremetric ∣ (λ _ _ → isPropIsPremetric _) ])
    where
    open PremetricStr
    open IsIsometry

    ternRel = autoDUARel (𝒮-Univ _) (λ A → A → ℚ₊ → A → Type ℓ')

  PremetricSIP : (M N : PremetricSpace ℓ ℓ') → Isometry[ M , N ] ≃ (M ≡ N)
  PremetricSIP = ∫ 𝒮ᴰ-Premetric .UARel.ua
