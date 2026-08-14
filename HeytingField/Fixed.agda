{-# OPTIONS --safe #-}

module HeytingField.Fixed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Subgroup

open import HeytingField.Base
open import HeytingField.Extension.Base
open import HeytingField.Extension.Morphism
open import HeytingField.Extension.Subextension
open import HeytingField.Properties
open import HeytingField.Subfield

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  F E : HeytingField ℓ ℓ'
  F→E : HeytingFieldHom F E

module OfAutomorphism (((e , eIsHom) , eIsFHom) : ExtensionAut F (E , F→E)) where
  private
    module F = FieldTheory F
    module E = FieldTheory E
    module e = IsExtensionHom eIsFHom

  Fixed : ⟨ E ⟩ → Type _
  Fixed x = equivFun e x ≡ x

  open isSubextension
  open isSubfield

  isSubextensionFixed : isSubextension F (E , F→E) Fixed
  isSubextensionFixed .is-subfield .is-prop-valued x = E.is-set (equivFun e x) x
  isSubextensionFixed .is-subfield .0Closed = e.pres0
  isSubextensionFixed .is-subfield .+Closed x y xf yf = e.pres+ x y ∙ cong₂ E._+_ xf yf
  isSubextensionFixed .is-subfield .-Closed x xf = e.pres- x ∙ cong E.-_ xf
  isSubextensionFixed .is-subfield .1Closed = e.pres1
  isSubextensionFixed .is-subfield .·Closed x y xf yf = e.pres· x y ∙ cong₂ E._·_ xf yf
  isSubextensionFixed .is-subfield .recipClosed x x#0 xf = cong fst (inverseUniqueness x (_ , lemma) (_ , E.isRInvRecip x x#0))
    where
      open Units (HeytingField→CommRing E)
      lemma = sym (e.pres· _ _ ∙ congL E._·_ xf) ∙∙ cong (equivFun e) (E.isRInvRecip x x#0) ∙∙ e.pres1
  isSubextensionFixed .incClosed = e.presInc

  FixedSubextension : Subextension F (E , F→E) _
  FixedSubextension = Fixed , isSubextensionFixed

  FixedSubfield : Subfield E _
  FixedSubfield = Fixed , isSubextensionFixed .is-subfield

  FixedExtension : FieldExtension F _ _
  FixedExtension = getSubextension F (E , F→E) FixedSubextension

  FixedField : HeytingField _ _
  FixedField = getSubfield E FixedSubfield

module OfSubgroup (S : Subgroup (ExtensionAutGroup F (E , F→E))) where

  Fixed : ⟨ E ⟩ → Type _
  Fixed x = (e : ExtensionAut F (E , F→E)) → e ∈ ⟪ S ⟫ → OfAutomorphism.Fixed e x

  open isSubextension
  open isSubfield

  isSubextensionFixed : isSubextension F (E , F→E) Fixed
  isSubextensionFixed = isSubextensionIntersection λ e → isSubextensionIntersection λ _ → OfAutomorphism.isSubextensionFixed e

  FixedSubextension : Subextension F (E , F→E) _
  FixedSubextension = Fixed , isSubextensionFixed

  FixedSubfield : Subfield E _
  FixedSubfield = Fixed , isSubextensionFixed .is-subfield

  FixedExtension : FieldExtension F _ _
  FixedExtension = getSubextension F (E , F→E) FixedSubextension

  FixedField : HeytingField _ _
  FixedField = getSubfield E FixedSubfield
