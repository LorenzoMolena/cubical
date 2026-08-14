{-# OPTIONS --safe #-}
module HeytingField.Polynomials.Division where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; separatedℕ; predℕ)
open import Cubical.Data.Nat.Order as ℕOrd
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Properties
open import Cubical.Algebra.Polynomials.UnivariateList.UniversalProperty
open import Cubical.Algebra.OrderedCommMonoid
open import Cubical.Algebra.OrderedCommMonoid.Instances
open import Cubical.Algebra.OrderedCommMonoid.PropCompletion
open import Cubical.Relation.Nullary
open import Cubical.Tactics.CommRingSolver
open import Cubical.Reflection.RecordEquiv

open import HeytingField.Base
open import HeytingField.Properties
open import HeytingField.Polynomials.Degree

module FieldPolyDivision (F : HeytingField ℓ-zero ℓ-zero) where
  open FieldTheory F
  open PolyModTheory FCRing
  open PolyMod FCRing using (Poly→Prf; ElimProp; isSetPoly) renaming (Poly→Fun to coefficent)
  open Exponentiation FCRing
  open FieldPoly F

  record QuotRem (f g : Poly FCRing) : Type where
    constructor makeQuotRem
    field
      quot rem : Poly FCRing
      prf : f ≡ (quot Poly* g) Poly+ rem
  
  open QuotRem public

  unquoteDecl QuotRemIsoΣ = declareRecordIsoΣ QuotRemIsoΣ (quote QuotRem)

  -- Theorem 5.2
  div : ∀ f g m n → f hasDeg≤ m → g hasDeg≤ n → (p : n ≤ suc m)
      → Σ[ qr ∈ QuotRem ((coefficent g n ^ p .fst) PolyConst* f) g ] qr .rem hasDeg< m
  div f g m n df≤m dg<m (zero , n≡sm) = makeQuotRem 0P f (PolyConst*Lid f ∙ sym (Poly+Lid f)) , {!   !}
  div f g m n df<n dg<m (suc k , sk+n≡sm) = {!   !}