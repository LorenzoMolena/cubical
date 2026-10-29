module Cubical.Algebra.VectorSpace.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Module
open import Cubical.Algebra.HeytingField.Base
open import Cubical.Algebra.HeytingField.Properties

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level

VectorSpace : (F : HeytingField ℓ ℓ') → ∀ ℓ'' → Type (ℓ-max ℓ (ℓ-suc ℓ''))
VectorSpace F ℓ'' = Σ[ A ∈ Type ℓ'' ] LeftModuleStr (HeytingField→Ring F) A

VectorSpaceHom : {F : HeytingField ℓ ℓ'} (V W : VectorSpace F ℓ'') → Type (ℓ-max ℓ ℓ'')
VectorSpaceHom V W = LeftModuleHom V W

VectorSpaceEquiv : {F : HeytingField ℓ ℓ'} (V W : VectorSpace F ℓ'') → Type (ℓ-max ℓ ℓ'')
VectorSpaceEquiv V W = LeftModuleEquiv V W

isPropIsVectorSpace : (F : HeytingField ℓ ℓ') {V : Type ℓ''}
  (0v : V)
  (_+_ : V → V → V)
  (-_ : V → V)
  (_⋆_ : ⟨ F ⟩ → V → V)
  → isProp (IsLeftModule (HeytingField→Ring F) 0v _+_ -_ _⋆_)
isPropIsVectorSpace F = isPropIsLeftModule (HeytingField→Ring F)

VectorSpacePath : {F : HeytingField ℓ ℓ'} (V W : VectorSpace F ℓ'')
                → (VectorSpaceEquiv {F = F} V W) ≃ (V ≡ W)
VectorSpacePath {F = F} = ∫ (𝒮ᴰ-LeftModule (HeytingField→Ring F)) .UARel.ua
