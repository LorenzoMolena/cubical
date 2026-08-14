{-# OPTIONS --safe #-}
module HeytingField.Extension.Algebraic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Properties

open import HeytingField.Base
open import HeytingField.Properties

open import HeytingField.Polynomials.Base

open import HeytingField.Extension.Base
open import HeytingField.Extension.Morphism

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level

module Algebraic (F : HeytingField ℓ ℓ') (Ext@(E , F→E , F→EIsHom) : FieldExtension F ℓ'' ℓ''') where
  private
    module F = FieldTheory F
    module E = FieldTheory E
    FPoly = Poly F.FCRing
  open PolyMod F.FCRing
  open FieldPoly F
  open Evaluation Ext

  -- An element of E is algebraic if it satisfies some monic polynomial over F
  isAlgebraicEl : ⟨ E ⟩ → Type (ℓ-max ℓ ℓ'')
  isAlgebraicEl x = ∃[ P ∈ FPoly ] isMonic P × isRoot P x

  isAlgebraicElWithDeg : ⟨ E ⟩ → ℕ → Type (ℓ-max ℓ ℓ'')
  isAlgebraicElWithDeg x n = ∃[ P ∈ FPoly ] P isMonicWithDeg≡ n × isRoot P x

  isAlgebraicElWithDeg→isAlgebraicEl : ∀ x n → isAlgebraicElWithDeg x n → isAlgebraicEl x
  isAlgebraicElWithDeg→isAlgebraicEl x n = PT.map (map-snd (map-fst (n ,_)))

  isAlgebraicClosed : Type (ℓ-max ℓ ℓ'')
  isAlgebraicClosed = ∀ x → isAlgebraicEl x → fiber F→E x

  isPropIsAlgebraicClosed : isProp isAlgebraicClosed
  isPropIsAlgebraicClosed = isPropΠ2 λ _ _ → isEmbedding→hasPropFibers (injEmbedding E.is-set (FieldHomIsInj (F→E , F→EIsHom) _ _)) _

  isAlgebraicExt : Type (ℓ-max ℓ ℓ'')
  isAlgebraicExt = ∀ x → isAlgebraicEl x

  isPropIsAlgebraicExt : isProp isAlgebraicExt
  isPropIsAlgebraicExt = isPropΠ λ _ → isPropPropTrunc

  -- This is outside the scope of this project
  -- isSubfieldAlgebraicEl
  
