{-# OPTIONS --safe #-}

module HeytingField.Extension.Subextension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import HeytingField.Base
open import HeytingField.Properties
open import HeytingField.Subfield

open import HeytingField.Extension.Base
open import HeytingField.Extension.Morphism

private variable
  ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ''''' : Level

module _ (F : HeytingField ℓ ℓ') ((E , f , fIsHom) : FieldExtension F ℓ'' ℓ''') where

  record isSubextension (S : ⟨ E ⟩ → Type ℓ'''') : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ'') ℓ''') ℓ'''') where
    field
      is-subfield : isSubfield E S
      incClosed : ∀ x → S (f x) -- This actually implies that it contains 0 and 1
    
    open isSubfield is-subfield public
  
  open isSubextension
  
  Subextension : ∀ ℓ'''' → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ'') ℓ''') (ℓ-suc ℓ''''))
  Subextension ℓ'''' = Σ[ S ∈ (⟨ E ⟩ → Type ℓ'''') ] isSubextension S

  getSubextension : Subextension ℓ'''' → FieldExtension F (ℓ-max ℓ'' ℓ'''') ℓ'''
  getSubextension (S , Ss) = getSubfield E (S , Ss.is-subfield) ,
    makeFieldHom (λ x → _ , Ss.incClosed x) (λ x y → S≡ (f.pres+ x y)) (S≡ f.pres1) (λ x y → S≡ (f.pres· x y)) λ x y →
      invEq (f.pres# x y)
    where
      module Ss = isSubextension Ss
      S≡ = Σ≡Prop Ss.is-prop-valued
      module f = IsHeytingFieldHom fIsHom
  
  getSubextensionEmb : (S : Subextension ℓ'''') → ExtensionHom F (getSubextension S) (E , f , fIsHom)
  getSubextensionEmb (S , Ss) = getSubfieldEmb E (S , is-subfield Ss) , makeIsExtensionHom (λ x → refl)

  Subextension' : ∀ ℓ'''' → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ'') (ℓ-suc ℓ''')) (ℓ-suc ℓ''''))
  Subextension' ℓ'''' = Σ[ S ∈ FieldExtension F ℓ'''' ℓ''' ] ExtensionHom F S (E , f , fIsHom)

  Subextension→Subextension' : Subextension ℓ'''' → Subextension' (ℓ-max ℓ'' ℓ'''')
  Subextension→Subextension' S = getSubextension S , getSubextensionEmb S

module _ {F : HeytingField ℓ ℓ'} {(E , f , fIsHom) : FieldExtension F ℓ'' ℓ'''} where
  
  open isSubextension

  isSubextensionIntersection : {A : Type ℓ'''''} {P : A → ⟨ E ⟩ → Type ℓ''''}
                             → (∀ a → isSubextension F (E , f , fIsHom) (P a))
                             → isSubextension F (E , f , fIsHom) λ x → ∀ a → P a x
  isSubextensionIntersection P .is-subfield = isSubfieldIntersection (λ a → P a .is-subfield)
  isSubextensionIntersection P .incClosed x a = P a .incClosed x