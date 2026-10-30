{- A vector space is defined as a LeftModule over the underlying ring of an
  heyting field. This module just defines aliases for definitions and properties
  of left modules, so that we don't have to write `HeytingField→Ring` every time -}
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

-- aliases
module _ (F : HeytingField ℓ ℓ') where
  module _ {V : Type ℓ''} (0v : V) (_+_ : V → V → V) (-_ : V → V) (_⋆_ : ⟨ F ⟩ → V → V) where
    IsVectorSpace : Type (ℓ-max ℓ ℓ'')
    IsVectorSpace = IsLeftModule (HeytingField→Ring F) 0v _+_ -_ _⋆_

  module _ (V : Type ℓ'') where
    VectorSpaceStr : Type (ℓ-max ℓ ℓ'')
    VectorSpaceStr = LeftModuleStr (HeytingField→Ring F) V

VectorSpace : (F : HeytingField ℓ ℓ') → ∀ ℓ'' → Type (ℓ-max ℓ (ℓ-suc ℓ''))
VectorSpace F ℓ'' = Σ[ A ∈ Type ℓ'' ] VectorSpaceStr F A

VectorSpaceHom : {F : HeytingField ℓ ℓ'} (V W : VectorSpace F ℓ'') → Type (ℓ-max ℓ ℓ'')
VectorSpaceHom V W = LeftModuleHom V W

VectorSpaceEquiv : {F : HeytingField ℓ ℓ'} (V W : VectorSpace F ℓ'') → Type (ℓ-max ℓ ℓ'')
VectorSpaceEquiv V W = LeftModuleEquiv V W

isPropIsVectorSpace : (F : HeytingField ℓ ℓ') {V : Type ℓ''}
  (0v : V)
  (_+_ : V → V → V)
  (-_ : V → V)
  (_⋆_ : ⟨ F ⟩ → V → V)
  → isProp (IsVectorSpace F 0v _+_ -_ _⋆_)
isPropIsVectorSpace F = isPropIsLeftModule (HeytingField→Ring F)

𝒮ᴰ-VectorSpace :
  (F : HeytingField ℓ ℓ') → DUARel (𝒮-Univ ℓ'') (VectorSpaceStr F) (ℓ-max ℓ ℓ'')
𝒮ᴰ-VectorSpace F = 𝒮ᴰ-LeftModule (HeytingField→Ring F)

VectorSpacePath : {F : HeytingField ℓ ℓ'} (V W : VectorSpace F ℓ'')
                → (VectorSpaceEquiv {F = F} V W) ≃ (V ≡ W)
VectorSpacePath {F = F} = ∫ (𝒮ᴰ-VectorSpace F) .UARel.ua
