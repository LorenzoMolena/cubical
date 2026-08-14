{-# OPTIONS --allow-unsolved-metas #-}

module HeytingField.Extension.Galois where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Group
open import Cubical.Data.Sigma

open import HeytingField.Base
open import HeytingField.Properties

open import HeytingField.Extension.Base
open import HeytingField.Extension.Algebraic
open import HeytingField.Extension.Morphism

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  F : HeytingField ℓ ℓ'

module _ (F : HeytingField ℓ ℓ') (E : FieldExtension F ℓ'' ℓ''') where
  isSeparableExtension : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
  isSeparableExtension = {!!}

  isNormalExtension : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
  isNormalExtension = {!   !}

  isAlgebraicExtension : Type (ℓ-max ℓ ℓ'')
  isAlgebraicExtension = Algebraic.isAlgebraicExt F E

  isGaloisExtension : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
  isGaloisExtension =  isSeparableExtension × isNormalExtension × isAlgebraicExtension

SeparableExtension : ∀ (F : HeytingField ℓ ℓ') ℓ'' ℓ''' → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
SeparableExtension F ℓ'' ℓ''' = Σ[ E ∈ HeytingField ℓ'' ℓ''' ] Σ[ F→E ∈ HeytingFieldHom F E ] isSeparableExtension F (E , F→E)

AlgebraicExtension : ∀ (F : HeytingField ℓ ℓ') ℓ'' ℓ''' → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
AlgebraicExtension F ℓ'' ℓ''' = Σ[ E ∈ HeytingField ℓ'' ℓ''' ] Σ[ F→E ∈ HeytingFieldHom F E ] isAlgebraicExtension F (E , F→E)

GaloisExtension : ∀ (F : HeytingField ℓ ℓ') ℓ'' ℓ''' → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
GaloisExtension F ℓ'' ℓ''' = Σ[ E ∈ HeytingField ℓ'' ℓ''' ] Σ[ F→E ∈ HeytingFieldHom F E ] isGaloisExtension F (E , F→E)

GaloisExtension→Extension : GaloisExtension F ℓ'' ℓ''' → FieldExtension F ℓ'' ℓ'''
GaloisExtension→Extension (E , F→E , _) = (E , F→E)

GaloisGroup : (F : HeytingField ℓ ℓ') (E : GaloisExtension F (ℓ-max ℓ ℓ'') ℓ'')
            → Group (ℓ-max ℓ ℓ'')
GaloisGroup F E = ExtensionAutGroup F (GaloisExtension→Extension E)
