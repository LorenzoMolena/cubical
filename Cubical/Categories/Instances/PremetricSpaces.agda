{- Categories of premetric spaces with different kinds of mappings -}

module Cubical.Categories.Instances.PremetricSpaces where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP

open import Cubical.Categories.Category.Base as Cat

open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

module _ (ℓ ℓ' : Level) where
  open Category
  open PremetricStr

  PrSpacesᶜ : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  ob       PrSpacesᶜ = PremetricSpace ℓ ℓ'
  Hom[_,_] PrSpacesᶜ = C[_,_]
  id       PrSpacesᶜ = idᶜ
  _⋆_      PrSpacesᶜ = flip _∘C_
  ⋆IdL     PrSpacesᶜ = λ _ → C≡ refl
  ⋆IdR     PrSpacesᶜ = λ _ → C≡ refl
  ⋆Assoc   PrSpacesᶜ = λ _ _ _ → C≡ refl
  isSetHom PrSpacesᶜ {y = N} =
    isSetΣSndProp (isSet→ (N .snd .isSetM)) (flip (isPropIsContinuous _) _)

  PrSpacesᵘᶜ : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  ob       PrSpacesᵘᶜ = PremetricSpace ℓ ℓ'
  Hom[_,_] PrSpacesᵘᶜ = UC[_,_]
  id       PrSpacesᵘᶜ = idᵘᶜ
  _⋆_      PrSpacesᵘᶜ = flip _∘UC_
  ⋆IdL     PrSpacesᵘᶜ = λ _ → UC≡ refl
  ⋆IdR     PrSpacesᵘᶜ = λ _ → UC≡ refl
  ⋆Assoc   PrSpacesᵘᶜ = λ _ _ _ → UC≡ refl
  isSetHom PrSpacesᵘᶜ {y = N} =
    isSetΣSndProp (isSet→ (N .snd .isSetM)) (flip (isPropIsUContinuous _) _)

  PrSpacesᴸ : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  ob       PrSpacesᴸ = PremetricSpace ℓ ℓ'
  Hom[_,_] PrSpacesᴸ = L[_,_]
  id       PrSpacesᴸ = idᴸ
  _⋆_      PrSpacesᴸ = flip _∘L_
  ⋆IdL     PrSpacesᴸ = λ _ → L≡ refl
  ⋆IdR     PrSpacesᴸ = λ _ → L≡ refl
  ⋆Assoc   PrSpacesᴸ = λ _ _ _ → L≡ refl
  isSetHom PrSpacesᴸ {y = N} =
    isSetΣSndProp (isSet→ (N .snd .isSetM)) (flip (isPropIsLipschitz _) _)

  PrSpacesⁿ : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  ob       PrSpacesⁿ = PremetricSpace ℓ ℓ'
  Hom[_,_] PrSpacesⁿ = NE[_,_]
  id       PrSpacesⁿ = idⁿ
  _⋆_      PrSpacesⁿ = flip _∘NE_
  ⋆IdL     PrSpacesⁿ = λ _ → NE≡ refl
  ⋆IdR     PrSpacesⁿ = λ _ → NE≡ refl
  ⋆Assoc   PrSpacesⁿ = λ _ _ _ → NE≡ refl
  isSetHom PrSpacesⁿ {y = N} =
    isSetΣSndProp (isSet→ (N .snd .isSetM)) (flip (isPropIsNonExpansive _) _)

module _ {ℓ ℓ'} {M N : PremetricSpace ℓ ℓ'} where
  open Cat.isIso
  open Iso

  private
    module M = PremetricStr (M .snd)
    module N = PremetricStr (N .snd)

  CatIsoⁿ→CatIsoᴸ : CatIso (PrSpacesⁿ ℓ ℓ') M N → CatIso (PrSpacesᴸ ℓ ℓ') M N
  fst (CatIsoⁿ→CatIsoᴸ f)       = NE→L (fst f)
  inv (snd (CatIsoⁿ→CatIsoᴸ f)) = NE→L (inv (snd f))
  sec (snd (CatIsoⁿ→CatIsoᴸ f)) = L≡ (cong fst (sec (snd f)))
  ret (snd (CatIsoⁿ→CatIsoᴸ f)) = L≡ (cong fst (ret (snd f)))

  CatIsoⁿ→CatIsoᵘᶜ : CatIso (PrSpacesⁿ ℓ ℓ') M N → CatIso (PrSpacesᵘᶜ ℓ ℓ') M N
  fst (CatIsoⁿ→CatIsoᵘᶜ f)       = NE→UC (fst f)
  inv (snd (CatIsoⁿ→CatIsoᵘᶜ f)) = NE→UC (inv (snd f))
  sec (snd (CatIsoⁿ→CatIsoᵘᶜ f)) = UC≡ (cong fst (sec (snd f)))
  ret (snd (CatIsoⁿ→CatIsoᵘᶜ f)) = UC≡ (cong fst (ret (snd f)))

  CatIsoᴸ→CatIsoᵘᶜ : CatIso (PrSpacesᴸ ℓ ℓ') M N → CatIso (PrSpacesᵘᶜ ℓ ℓ') M N
  fst (CatIsoᴸ→CatIsoᵘᶜ f)       = L→UC (fst f)
  inv (snd (CatIsoᴸ→CatIsoᵘᶜ f)) = L→UC (inv (snd f))
  sec (snd (CatIsoᴸ→CatIsoᵘᶜ f)) = UC≡ (cong fst (sec (snd f)))
  ret (snd (CatIsoᴸ→CatIsoᵘᶜ f)) = UC≡ (cong fst (ret (snd f)))

  CatIsoᵘᶜ→CatIsoᶜ : CatIso (PrSpacesᵘᶜ ℓ ℓ') M N → CatIso (PrSpacesᶜ ℓ ℓ') M N
  fst (CatIsoᵘᶜ→CatIsoᶜ f)       = UC→C (fst f)
  inv (snd (CatIsoᵘᶜ→CatIsoᶜ f)) = UC→C (inv (snd f))
  sec (snd (CatIsoᵘᶜ→CatIsoᶜ f)) = C≡ (cong fst (sec (snd f)))
  ret (snd (CatIsoᵘᶜ→CatIsoᶜ f)) = C≡ (cong fst (ret (snd f)))

  CatIsoⁿ→CatIsoᶜ : CatIso (PrSpacesⁿ ℓ ℓ') M N → CatIso (PrSpacesᶜ ℓ ℓ') M N
  CatIsoⁿ→CatIsoᶜ = CatIsoᵘᶜ→CatIsoᶜ ∘ CatIsoⁿ→CatIsoᵘᶜ

  CatIsoᴸ→CatIsoᶜ : CatIso (PrSpacesᴸ ℓ ℓ') M N → CatIso (PrSpacesᶜ ℓ ℓ') M N
  CatIsoᴸ→CatIsoᶜ = CatIsoᵘᶜ→CatIsoᶜ ∘ CatIsoᴸ→CatIsoᵘᶜ

  isCatIso→Isometry : (f : NE[ M , N ])
    → Cat.isIso (PrSpacesⁿ ℓ ℓ') f
    → Isometry[ M , N ]
  isCatIso→Isometry f fiso = isoToEquiv isom , isisometry pres
    where
    open Cat.isIso fiso renaming (inv to invⁿ ; sec to secⁿ ; ret to retⁿ)

    isom : Iso ⟨ M ⟩ ⟨ N ⟩
    isom .fun = fst f
    isom .inv = fst invⁿ
    isom .sec = funExt⁻ (cong fst secⁿ)
    isom .ret = funExt⁻ (cong fst retⁿ)

    pres : ∀ x ε y → x M.≈[ ε ] y ≃ isoToEquiv isom .fst x N.≈[ ε ] isoToEquiv isom .fst y
    pres x ε y = propBiimpl→Equiv
      (M.isProp≈ x y ε)
      (N.isProp≈ (fst f x) (fst f y) ε)
      (IsNonExpansive.pres≈ (snd f) x y ε)
      (subst2 M._≈[ ε ]_ (funExt⁻ (cong fst retⁿ) x) (funExt⁻ (cong fst retⁿ) y)
        ∘ IsNonExpansive.pres≈ (snd invⁿ) (fst f x) (fst f y) ε)

  CatIso→Isometry : CatIso (PrSpacesⁿ ℓ ℓ') M N → Isometry[ M , N ]
  CatIso→Isometry = uncurry isCatIso→Isometry

  Isometry→CatIso : Isometry[ M , N ] → CatIso (PrSpacesⁿ ℓ ℓ') M N
  fst (Isometry→CatIso e) = Isometry→NE e
  isIso.inv (snd (Isometry→CatIso e)) = Isometry→NE (invIsometry e)
  isIso.sec (snd (Isometry→CatIso e)) = NE≡ (funExt (secEq (fst e)))
  isIso.ret (snd (Isometry→CatIso e)) = NE≡ (funExt (retEq (fst e)))

  PrSpacesⁿCatIso≃Isometry : CatIso (PrSpacesⁿ ℓ ℓ') M N ≃ Isometry[ M , N ]
  PrSpacesⁿCatIso≃Isometry = isoToEquiv isom
    where
    isom : Iso (CatIso (PrSpacesⁿ ℓ ℓ') M N) (Isometry[ M , N ])
    isom .fun = CatIso→Isometry
    isom .inv = Isometry→CatIso
    isom .sec = λ _ → Σ≡Prop (λ _ → isPropIsIsometry _ _ _) (equivEq refl)
    isom .ret = λ _ → CatIso≡ _ _ (NE≡ refl)

isUnivalentPrSpacesⁿ : ∀ {ℓ ℓ'} → isUnivalent (PrSpacesⁿ ℓ ℓ')
isUnivalent.univ isUnivalentPrSpacesⁿ M N =
  precomposesToId→Equiv pathToIso _
    (funExt (CatIso≡ _ _ ∘ NE≡ ∘ λ _ → transportRefl _))
    (snd (PrSpacesⁿCatIso≃Isometry ∙ₑ PremetricSIP M N))
