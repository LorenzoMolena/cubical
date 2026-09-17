module Cubical.Algebra.ArchimedeanField.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.HeytingField
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Morphisms
open import Cubical.Algebra.OrderedField.Base
open import Cubical.Algebra.OrderedField.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' ℓ'' ℓ<≤ ℓ<≤' ℓ<≤'' : Level

record IsArchimedeanField
  {F : Type ℓ}
  (0f 1f : F)
  (_+_ _·_ : F → F → F)
  (-_ : F → F)
  (_<_ _≤_ : F → F → Type ℓ')
  (ι : ℚ → F) : Type (ℓ-max ℓ ℓ') where
  constructor isarchimedeanfield
  field
    isOrderedField : IsOrderedField 0f 1f _+_ _·_ -_ _<_ _≤_
    isHomomorphism : IsOrderedFieldHom (snd ℚOrderedField) ι
                      (orderedfieldstr _ _ _ _ _ _ _ isOrderedField)
    archimedeanProperty : (x y : F) → x < y → ∃[ q ∈ ℚ ] (x < ι q) × (ι q < y)

  open IsOrderedField isOrderedField public
  open IsOrderedCommRingMono isHomomorphism public
    renaming
      ( isOrderedCommRingHom to isOrderedCommRingHomι ;
        isCommRingHom to isCommRingHomι ;
        pres0 to ιpres0 ;
        pres1 to ιpres1 ;
        pres+ to ιpres+ ;
        pres· to ιpres· ;
        pres- to ιpres- ;
        pres≤ to ιpres≤ ;
        reflect< to ιreflect< ;
        pres< to ιpres<)

record ArchimedeanFieldStr (ℓ' : Level) (F : Type ℓ) :
  Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor archimedeanfieldstr
  field
    0f 1f : F
    _+_ _·_ : F → F → F
    -_ : F → F
    _<_ _≤_ : F → F → Type ℓ'
    ι : ℚ → F
    isArchimedeanField : IsArchimedeanField 0f 1f _+_ _·_ -_ _<_ _≤_ ι

  open IsArchimedeanField isArchimedeanField public

  infix 8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix 4 _<_ _≤_

ArchimedeanField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
ArchimedeanField ℓ ℓ' = TypeWithStr ℓ (ArchimedeanFieldStr ℓ')

ArchimedeanField→OrderedField : ArchimedeanField ℓ ℓ' → OrderedField ℓ ℓ'
fst (ArchimedeanField→OrderedField F) = fst F
snd (ArchimedeanField→OrderedField F) = orderedfieldstr _ _ _ _ _ _ _ isOrderedField
  where open ArchimedeanFieldStr (snd F)

ArchimedeanField→HeytingField : ArchimedeanField ℓ ℓ' → HeytingField ℓ ℓ'
ArchimedeanField→HeytingField =
  OrderedField→HeytingField ∘ ArchimedeanField→OrderedField

ArchimedeanField→OrderedCommRing : ArchimedeanField ℓ ℓ' → OrderedCommRing ℓ ℓ'
ArchimedeanField→OrderedCommRing =
  OrderedField→OrderedCommRing ∘ ArchimedeanField→OrderedField

ArchimedeanField→CommRing : ArchimedeanField ℓ ℓ' → CommRing ℓ
ArchimedeanField→CommRing = OrderedCommRing→CommRing ∘ ArchimedeanField→OrderedCommRing

ArchimedeanField→Ring : ArchimedeanField ℓ ℓ' → Ring ℓ
ArchimedeanField→Ring = CommRing→Ring ∘ ArchimedeanField→CommRing

IsArchimedeanOrderedField : OrderedField ℓ ℓ' → Type (ℓ-max ℓ ℓ')
IsArchimedeanOrderedField F =
  Σ[ ι ∈ (ℚ → ⟨ F ⟩) ]
    IsOrderedFieldHom (snd ℚOrderedField) ι (snd F) ×
    ((x y : ⟨ F ⟩) → x < y → ∃[ q ∈ ℚ ] (x < ι q) × (ι q < y))
  where open OrderedFieldStr (snd F)

OrderedField→ArchimedeanField :
  (F : OrderedField ℓ ℓ') → IsArchimedeanOrderedField F → ArchimedeanField ℓ ℓ'
fst (OrderedField→ArchimedeanField F _) = fst F
snd (OrderedField→ArchimedeanField F (ι , isOFHom , archi)) =
  archimedeanfieldstr _ _ _ _ _ _ _ ι (isarchimedeanfield isOrderedField isOFHom archi)
  where open OrderedFieldStr (snd F)

module _ {A : Type ℓ} {B : Type ℓ'} where
  IsArchimedeanFieldHom : ArchimedeanFieldStr ℓ<≤ A → (A → B) → ArchimedeanFieldStr ℓ<≤' B → Type _
  IsArchimedeanFieldHom F f K = IsOrderedCommRingMono
    (snd (ArchimedeanField→OrderedCommRing (_ , F)))
    f
    (snd (ArchimedeanField→OrderedCommRing (_ , K)))

ArchimedeanFieldHom : ArchimedeanField ℓ ℓ<≤ → ArchimedeanField ℓ' ℓ<≤' → Type _
ArchimedeanFieldHom F K =
  Σ[ f ∈ (⟨ F ⟩ → ⟨ K ⟩) ] IsArchimedeanFieldHom (F .snd) f (K .snd)

idAFHom : (F : ArchimedeanField ℓ ℓ<≤) → ArchimedeanFieldHom F F
idAFHom = idOCRMono ∘ ArchimedeanField→OrderedCommRing

module _
  {F : ArchimedeanField ℓ ℓ<≤}
  {K : ArchimedeanField ℓ' ℓ<≤'}
  {H : ArchimedeanField ℓ'' ℓ<≤''}
  where

  compAFHom : ArchimedeanFieldHom F K → ArchimedeanFieldHom K H → ArchimedeanFieldHom F H
  compAFHom = compOCRMono

  _∘af_ : ArchimedeanFieldHom K H → ArchimedeanFieldHom F K → ArchimedeanFieldHom F H
  _∘af_ = _∘ocr↪_
