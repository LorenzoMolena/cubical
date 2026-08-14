{-# OPTIONS --safe #-}

module HeytingField.Extension.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommAlgebra.AsModule
open import Cubical.Algebra.CommRing

open import HeytingField.Base
open import HeytingField.Properties

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level

module _ (F : HeytingField ℓ ℓ') where
  open FieldTheory F
  FieldExtension : ∀ ℓ'' ℓ''' → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
  FieldExtension ℓ'' ℓ''' = Σ[ E ∈ HeytingField ℓ'' ℓ''' ] HeytingFieldHom F E

  FieldExtension→CommAlg : FieldExtension ℓ'' ℓ''' → CommAlgebra FCRing ℓ''
  FieldExtension→CommAlg (E , F→E) = CommAlgChar.toCommAlg FCRing (HeytingField→CommRing E , RingHom→CommRingHom (HeytingFieldHom→RingHom F E F→E))
