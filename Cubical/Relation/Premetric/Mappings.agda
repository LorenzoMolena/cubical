module Cubical.Relation.Premetric.Mappings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP

open import Cubical.Categories.Category.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Int.Fast as ℤ
open import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚ

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)


open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Relation.Premetric.Base

private
  variable
    ℓM ℓM' ℓN ℓN' : Level

module ℚ₊Inverse where

  private
    ℚOCR = ℚOrderedCommRing
    ℚCR  = OrderedCommRing→CommRing ℚOCR
  open Units ℚCR
  open CommRingTheory ℚCR

  Σinverseℚ₊ : ((ε , 0<ε) : ℚ₊) → Σ[ δ ∈ ℚ ] (ε ℚ.· δ ≡ 1)
  Σinverseℚ₊ = uncurry $ SQ.elimProp (λ ε → isPropΠ λ _ → inverseUniqueness ε) λ
    { (pos zero    , 1+ d) p → ⊥.rec (ℤ.isIrrefl< p)
    ; (pos (suc n) , (1+ d)) p .fst → [ pos (suc d) / 1+ n ]
    ; (pos (suc n) , (1+ d)) p .snd →
      let 1+n = pos (suc n) ; 1+d = pos (suc d) ; 1+n·1+d = 1+ d ·₊₁ 1+ n
      in
      [ 1+n ℤ.· 1+d / 1+n·1+d ]  ≡⟨ cong [_/ 1+n·1+d ] (ℤ.·Comm 1+n 1+d) ⟩
      [ 1+d ℤ.· 1+n / 1+n·1+d ]  ≡⟨ ℚ.·CancelR (1+ n) ⟩
      [ 1+d / 1+ d ]             ≡⟨ sym $ cong₂ [_/_] (ℤ.·IdL 1+d) (·₊₁-identityˡ (1+ d))⟩
      [ 1 ℤ.· 1+d / 1 ·₊₁ 1+ d ] ≡⟨ ℚ.·CancelR (1+ d) ⟩
      [ 1 / 1 ]                         ∎
    ; (negsuc n    , 1+ d) p → ⊥.rec (ℤ.¬pos≤negsuc p) }

  infixl 7 _⁻¹₊

  _⁻¹₊ : ℚ₊ → ℚ₊
  fst (ε ⁻¹₊) = fst (Σinverseℚ₊ ε)
  snd (ε ⁻¹₊) = uncurry
    (SQ.elimProp
      (λ ε → isPropΠ λ p → ℚ.isProp< 0 (fst (Σinverseℚ₊ (ε , p))) )
      λ { (pos zero    , 1+ d) p → ⊥.rec (ℤ.isIrrefl< p)
        ; (pos (suc n) , 1+ d) p → ℤ.zero-<possuc
        ; (negsuc n    , 1+ d) p → ⊥.rec (ℤ.¬pos≤negsuc p) })
    ε

  _/_ : ℚ₊ → ℚ₊ → ℚ₊
  ε / L = ε ·₊ (L ⁻¹₊)

  ⁻¹inverse : ∀ ε → ⟨ ε / ε ⟩₊ ≡ 1
  ⁻¹inverse = snd ∘ Σinverseℚ₊

  ·/ : ∀ L ε → ⟨ L ·₊ (ε / L) ⟩₊ ≡ ⟨ ε ⟩₊
  ·/ L ε =
    ⟨ L ·₊ (ε ·₊ (L ⁻¹₊)) ⟩₊ ≡⟨ ·CommAssocl ⟨ L ⟩₊ ⟨ ε ⟩₊ ⟨ L ⁻¹₊ ⟩₊ ⟩
    ⟨ ε ·₊ (L ·₊ (L ⁻¹₊)) ⟩₊ ≡⟨ cong (⟨ ε ⟩₊ ℚ.·_) (⁻¹inverse L) ⟩
    ⟨ ε ⟩₊ ℚ.· 1             ≡⟨ ℚ.·IdR ⟨ ε ⟩₊ ⟩
    ⟨ ε ⟩₊                   ∎


module _
  {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A)
  (N : PremetricStr ℓN' B)
  (f : A → B)
  where

  open ℚ₊Inverse

  private
    module M = PremetricStr M
    module N = PremetricStr N

  isNonExpanding : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isNonExpanding = ∀ x y ε → x M.≈[ ε ] y → f x N.≈[ ε ] f y

  isPropIsNonExpanding : isProp isNonExpanding
  isPropIsNonExpanding = isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  isLipschitzWith : ℚ₊ → Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isLipschitzWith L = ∀ x y ε → x M.≈[ ε ] y → f x N.≈[ L ·₊ ε ] f y

  isPropIsLipschitzWith : ∀ L → isProp (isLipschitzWith L)
  isPropIsLipschitzWith L = isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  isLipschitz : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isLipschitz = ∃[ L ∈ ℚ₊ ] isLipschitzWith L

  isPropIsLipschitz : isProp isLipschitz
  isPropIsLipschitz = squash₁

  isContinuousAt : (x : A) → Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isContinuousAt x = ∀ ε → ∃[ δ ∈ ℚ₊ ] (∀ y → x M.≈[ δ ] y → f x N.≈[ ε ] f y)

  isPropIsContinuousAt : ∀ x → isProp (isContinuousAt x)
  isPropIsContinuousAt x = isPropΠ λ _ → squash₁

  isContinuous : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isContinuous = ∀ x → isContinuousAt x

  isPropIsContinuous : isProp isContinuous
  isPropIsContinuous = isPropΠ isPropIsContinuousAt

  isUniformlyContinuousWith : (ℚ₊ → ℚ₊) → Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isUniformlyContinuousWith μ = ∀ x y ε → x M.≈[ μ ε ] y → f x N.≈[ ε ] f y

  isPropIsUniformlyContinuousWith : ∀ μ → isProp (isUniformlyContinuousWith μ)
  isPropIsUniformlyContinuousWith μ = isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  isUniformlyContinuous : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isUniformlyContinuous = ∃[ μ ∈ (ℚ₊ → ℚ₊) ] isUniformlyContinuousWith μ

  isPropIsUniformlyContinuous : isProp isUniformlyContinuous
  isPropIsUniformlyContinuous = squash₁

  isLipschitz→isUniformlyContinuous : isLipschitz → isUniformlyContinuous
  isLipschitz→isUniformlyContinuous = PT.map
    λ { (L , is-lip) .fst → _/ L
      ; (L , is-lip) .snd → λ x y ε x≈y →
      N.subst≈ (f x) (f y) (·/ L ε)
      (is-lip x y (ε / L)
        (x≈y
          :> x M.≈[ ε / L ] y)
        :> f x N.≈[ L ·₊ (ε / L) ] f y)
      :> f x N.≈[ ε ] f y }

  isUniformlyContinuous→isContinuous : isUniformlyContinuous → isContinuous
  isUniformlyContinuous→isContinuous = PT.rec isPropIsContinuous
    λ (μ , is-uc) → λ x ε → ∣ μ ε , flip (is-uc x) ε ∣₁

  isLipschitz→isContinuous : isLipschitz → isContinuous
  isLipschitz→isContinuous =
    isUniformlyContinuous→isContinuous ∘ isLipschitz→isUniformlyContinuous


C[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
C[ (M , MPr) , (N , NPr) ] = Σ[ f ∈ (M → N) ] isContinuous MPr NPr f

UC[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
UC[ (M , MPr) , (N , NPr) ] = Σ[ f ∈ (M → N) ] isUniformlyContinuous MPr NPr f

L[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
L[ (M , MPr) , (N , NPr) ] = Σ[ f ∈ (M → N) ] isLipschitz MPr NPr f

module CategoryStructures where
  open OrderedCommRingStr (str ℚOrderedCommRing)

  idᶜ : ∀ {M : PremetricSpace ℓM ℓM'} → C[ M , M ]
  fst idᶜ = idfun _
  snd idᶜ = λ x ε → ∣ ε , (λ y → idfun _) ∣₁

  idᵘᶜ : ∀ {M : PremetricSpace ℓM ℓM'} → UC[ M , M ]
  fst idᵘᶜ = idfun _
  snd idᵘᶜ = ∣ idfun _ , (λ x y ε → idfun _) ∣₁

  idᴸ : ∀ {M : PremetricSpace ℓM ℓM'} → L[ M , M ]
  fst (idᴸ {M = M}) = idfun ⟨ M ⟩
  snd (idᴸ {M = M}) = ∣ (1 , 0<1) , (λ x y ε → subst≈ x y (sym (ℚ.·IdL ⟨ ε ⟩₊))) ∣₁
    where open PremetricStr (str M)

  _∘C_ : ∀ {M N O : PremetricSpace ℓM ℓM'} → C[ N , O ] → C[ M , N ] → C[ M , O ]
  fst (_∘C_ (g , g-c) (f , f-c)) = g ∘ f
  snd (_∘C_ (g , g-c) (f , f-c)) = λ x ε → PT.rec squash₁ (λ
    { (δ , fx≈z→gfx≈gz) → PT.map (λ
    { (η , x≈y→fx≈fy)   → η , λ y → fx≈z→gfx≈gz (f y) ∘ x≈y→fx≈fy y })
    (f-c x δ) })
    (g-c (f x) ε)

  _∘UC_ : ∀ {M N O : PremetricSpace ℓM ℓM'} → UC[ N , O ] → UC[ M , N ] → UC[ M , O ]
  fst (_∘UC_ (g , g-uc) (f , f-uc)) = g ∘ f
  snd (_∘UC_ (g , g-uc) (f , f-uc)) = PT.map2 (λ
    { (μ , μ-uc) (ν , ν-uc) .fst       → μ ∘ ν
    ; (μ , μ-uc) (ν , ν-uc) .snd x y ε → ν-uc (f x) (f y) ε ∘ μ-uc x y (ν ε) })
    f-uc g-uc

  _∘L_ : ∀ {M N O : PremetricSpace ℓM ℓM'} → L[ N , O ] → L[ M , N ] → L[ M , O ]
  fst (_∘L_ {O = O} (g , g-lip) (f , f-lip)) = g ∘ f
  snd (_∘L_ {O = O} (g , g-lip) (f , f-lip)) = PT.map2 (λ
    { (L , L-lip) (R , R-lip) .fst       → R ·₊ L
    ; (L , L-lip) (R , R-lip) .snd x y ε →
        subst≈ (g (f x)) (g (f y)) (ℚ.·Assoc ⟨ R ⟩₊ ⟨ L ⟩₊ _)
      ∘ R-lip (f x) (f y) (L ·₊ ε)
      ∘ L-lip x y ε })
    f-lip g-lip
    where open PremetricStr (str O)

  lip≡ : ∀ {M N : PremetricSpace ℓM ℓM'} → {f g : L[ M , N ]} → fst f ≡ fst g → f ≡ g
  lip≡ = ΣPathPProp (λ _ → squash₁)

  uc≡ : ∀ {M N : PremetricSpace ℓM ℓM'} → {f g : UC[ M , N ]} → fst f ≡ fst g → f ≡ g
  uc≡ = ΣPathPProp (λ _ → squash₁)

  c≡ : ∀ {M N : PremetricSpace ℓM ℓM'} → {f g : C[ M , N ]} → fst f ≡ fst g → f ≡ g
  c≡ {M = M} {N} = ΣPathPProp (isPropIsContinuous (str M) (str N))

  module _ (ℓM ℓM' : Level) where
    open Category

    PremetricSpaceCategoryᶜ : Category (ℓ-suc (ℓ-max ℓM ℓM')) (ℓ-max ℓM ℓM')
    ob       PremetricSpaceCategoryᶜ                 = PremetricSpace ℓM ℓM'
    Hom[_,_] PremetricSpaceCategoryᶜ                 = C[_,_]
    id       PremetricSpaceCategoryᶜ {M}             = idᶜ {M = M}
    _⋆_      PremetricSpaceCategoryᶜ {M} {N} {O}     = flip (_∘C_ {M = M} {N} {O})
    ⋆IdL     PremetricSpaceCategoryᶜ {M} {N}         = λ _ → c≡ {M = M} {N} refl
    ⋆IdR     PremetricSpaceCategoryᶜ {M} {N}         = λ _ → c≡ {M = M} {N} refl
    ⋆Assoc   PremetricSpaceCategoryᶜ {M} {N} {O} {P} = λ _ _ _ → c≡ {M = M} {P} refl
    isSetHom PremetricSpaceCategoryᶜ {M} {N}         =
      isSetΣSndProp (isSet→ isSetM) (isPropIsContinuous (str M) (str N))
      where open PremetricStr (str N)

    PremetricSpaceCategoryᵘᶜ : Category (ℓ-suc (ℓ-max ℓM ℓM')) (ℓ-max ℓM ℓM')
    ob       PremetricSpaceCategoryᵘᶜ                 = PremetricSpace ℓM ℓM'
    Hom[_,_] PremetricSpaceCategoryᵘᶜ                 = UC[_,_]
    id       PremetricSpaceCategoryᵘᶜ {M}             = idᵘᶜ {M = M}
    _⋆_      PremetricSpaceCategoryᵘᶜ {M} {N} {O}     = flip (_∘UC_ {M = M} {N} {O})
    ⋆IdL     PremetricSpaceCategoryᵘᶜ {M} {N}         = λ _ → uc≡ {M = M} {N} refl
    ⋆IdR     PremetricSpaceCategoryᵘᶜ {M} {N}         = λ _ → uc≡ {M = M} {N} refl
    ⋆Assoc   PremetricSpaceCategoryᵘᶜ {M} {N} {O} {P} = λ _ _ _ → uc≡ {M = M} {P} refl
    isSetHom PremetricSpaceCategoryᵘᶜ {M} {N}         =
      isSetΣSndProp (isSet→ isSetM) (isPropIsUniformlyContinuous (str M) (str N))
      where open PremetricStr (str N)

    PremetricSpaceCategoryᴸ : Category (ℓ-suc (ℓ-max ℓM ℓM')) (ℓ-max ℓM ℓM')
    ob       PremetricSpaceCategoryᴸ                 = PremetricSpace ℓM ℓM'
    Hom[_,_] PremetricSpaceCategoryᴸ                 = L[_,_]
    id       PremetricSpaceCategoryᴸ {M}             = idᴸ {M = M}
    _⋆_      PremetricSpaceCategoryᴸ {M} {N} {O}     = flip (_∘L_ {M = M} {N} {O})
    ⋆IdL     PremetricSpaceCategoryᴸ {M} {N}         = λ _ → lip≡ {M = M} {N} refl
    ⋆IdR     PremetricSpaceCategoryᴸ {M} {N}         = λ _ → lip≡ {M = M} {N} refl
    ⋆Assoc   PremetricSpaceCategoryᴸ {M} {N} {O} {P} = λ _ _ _ → lip≡ {M = M} {P} refl
    isSetHom PremetricSpaceCategoryᴸ {M} {N}         =
      isSetΣSndProp (isSet→ isSetM) (isPropIsLipschitz (str M) (str N))
      where open PremetricStr (str N)

record IsPremetricEquiv {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A) (e : A ≃ B) (N : PremetricStr ℓN' B)
  : Type (ℓ-suc (ℓ-max ℓM (ℓ-max ℓN (ℓ-max ℓM' ℓN'))))
  where
  constructor
   ispremetricequiv
  -- Shorter qualified names
  private
    module M = PremetricStr M
    module N = PremetricStr N

  field
    pres≈ : ∀ x y ε → x M.≈[ ε ] y ≃ equivFun e x N.≈[ ε ] equivFun e y
