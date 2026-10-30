{- Normed Space over a valued field -}
module Cubical.Algebra.NormedSpace.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP

open import Cubical.Algebra.ArchimedeanField.Base
open import Cubical.Algebra.Module
open import Cubical.Algebra.ValuedField.Base
open import Cubical.Algebra.VectorSpace.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ# ℓ<≤ ℓ<≤' : Level

record IsNormedSpace (R : ArchimedeanField ℓ' ℓ<≤) (F : ValuedField R ℓ'' ℓ#)
  {V : Type ℓ}
  (0v : V)
  (_+_ : V → V → V)
  (-_ : V → V)
  (_⋆_ : ⟨ F ⟩ → V → V)
  (∥_∥ : V → ⟨ R ⟩)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' (ℓ-max ℓ# ℓ<≤)))) where
  no-eta-equality
  constructor isnormedspace
  open ValuedFieldStr (snd F) using (∣_∣)
  open ArchimedeanFieldStr (snd R) using (_≤_ ; _·_) renaming (0f to 0r ; _+_ to _+r_)
  field
    isVectorSpace     : IsVectorSpace (ValuedField→HeytingField F) 0v _+_ -_ _⋆_
    isNonNegative∥    : ∀ v   → 0r ≤ ∥ v ∥
    isMultiplicative∥ : ∀ k v → ∥ k ⋆ v ∥ ≡ ∣ k ∣ · ∥ v ∥
    isTriangular∥     : ∀ v w → ∥ v + w ∥ ≤ ∥ v ∥ +r ∥ w ∥
    isSeparated∥      : ∀ v   → ∥ v ∥ ≡ 0r → v ≡ 0v

  open IsLeftModule isVectorSpace public

record NormedSpaceStr (R : ArchimedeanField ℓ' ℓ<≤) (F : ValuedField R ℓ'' ℓ#)
  (V : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' (ℓ-max ℓ# ℓ<≤))))) where
  constructor normedspacestr
  field
    0v  : V
    _+_ : V → V → V
    -_  : V → V
    _⋆_ : ⟨ F ⟩ → V → V
    ∥_∥ : V → ⟨ R ⟩
    isNormedSpace : IsNormedSpace R F 0v _+_ -_ _⋆_ ∥_∥

  infixr 7 _+_
  infix  8 -_
  infix  9 _⋆_

  open IsNormedSpace isNormedSpace public

module _ (R : ArchimedeanField ℓ' ℓ<≤) (F : ValuedField R ℓ'' ℓ#) where

  NormedSpace : ∀ ℓ → Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' (ℓ-max ℓ# ℓ<≤)))))
  NormedSpace ℓ = TypeWithStr ℓ (NormedSpaceStr R F)

  NormedSpace→VectorSpace : NormedSpace ℓ → VectorSpace (ValuedField→HeytingField F) ℓ
  fst (NormedSpace→VectorSpace V) = fst V
  snd (NormedSpace→VectorSpace V) = vectorSpaceStr where
    open NormedSpaceStr (snd V)
    vectorSpaceStr : VectorSpaceStr (ValuedField→HeytingField F) (fst V)
    LeftModuleStr.0m           vectorSpaceStr = 0v
    LeftModuleStr._+_          vectorSpaceStr = _+_
    LeftModuleStr.-_           vectorSpaceStr = -_
    LeftModuleStr._⋆_          vectorSpaceStr = _⋆_
    LeftModuleStr.isLeftModule vectorSpaceStr = isVectorSpace
