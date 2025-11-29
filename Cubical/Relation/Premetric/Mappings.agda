module Cubical.Relation.Premetric.Mappings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Relation.Premetric.Base

private
  variable
    ℓM ℓM' ℓN ℓN' : Level

module _ where

  record IsNonExpanding {A : Type ℓM} {B : Type ℓN}
    (M : PremetricStr ℓM' A)
    (f : A → B)
    (N : PremetricStr ℓN' B)
    : Type (ℓ-suc (ℓ-max ℓM (ℓ-max ℓN (ℓ-max ℓM' ℓN'))))
    where
    no-eta-equality
    private
      module M = PremetricStr M
      module N = PremetricStr N

    field
      pres≈ : ∀ x y ε → x M.≈[ ε ] y → f x N.≈[ ε ] f y

  unquoteDecl IsNonExpandingIsoΣ = declareRecordIsoΣ IsNonExpandingIsoΣ (quote IsNonExpanding)

  record IsLipschitz {A : Type ℓM} {B : Type ℓN}
    (L : ℚ₊)
    (M : PremetricStr ℓM' A)
    (f : A → B)
    (N : PremetricStr ℓN' B)
    : Type (ℓ-suc (ℓ-max ℓM (ℓ-max ℓN (ℓ-max ℓM' ℓN'))))
    where
    no-eta-equality
    private
      module M = PremetricStr M
      module N = PremetricStr N

    field
      pres≈ : ∀ x y ε → x M.≈[ ε ] y → f x N.≈[ L ·₊ ε ] f y

  unquoteDecl IsLipschitzIsoΣ = declareRecordIsoΣ IsLipschitzIsoΣ (quote IsLipschitz)

  record IsUniformlyContinuous {A : Type ℓM} {B : Type ℓN}
    (μ : ℚ₊ → ℚ₊)
    (M : PremetricStr ℓM' A)
    (f : A → B)
    (N : PremetricStr ℓN' B)
    : Type (ℓ-suc (ℓ-max ℓM (ℓ-max ℓN (ℓ-max ℓM' ℓN'))))
    where
    no-eta-equality
    private
      module M = PremetricStr M
      module N = PremetricStr N

    field
      pres≈ : ∀ x y ε → x M.≈[ μ ε ] y → f x N.≈[ ε ] f y

  unquoteDecl IsUniformlyContinuousIsoΣ = declareRecordIsoΣ IsUniformlyContinuousIsoΣ (quote IsUniformlyContinuous)

  record IsPremetricEquiv {A : Type ℓM} {B : Type ℓN}
    (M : PremetricStr ℓM' A) (e : A ≃ B) (N : PremetricStr ℓN' B)
    : Type (ℓ-suc (ℓ-max ℓM (ℓ-max ℓN (ℓ-max ℓM' ℓN'))))
    where
    constructor
     istosetequiv
    -- Shorter qualified names
    private
      module M = PremetricStr M
      module N = PremetricStr N

    field
      pres≈ : ∀ x y ε → x M.≈[ ε ] y ≃ equivFun e x N.≈[ ε ] equivFun e y
