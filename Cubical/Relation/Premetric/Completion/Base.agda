open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Base {ℓ} {ℓ'}
  (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude

private
  M = M' .fst
  open PremetricStr (M' .snd)

data ℭ : Type (ℓ-max ℓ ℓ')
data _∼[_]_ : ℭ → ℚ₊ → ℭ → Type (ℓ-max ℓ ℓ')

data ℭ where
  ι   : M → ℭ
  lim : (x : ℚ₊ → ℭ) → (∀ ε δ → x ε ∼[ ε +₊ δ ] x δ) → ℭ
  eqℭ : ∀ x y → (∀ ε → x ∼[ ε ] y ) → x ≡ y

data _∼[_]_ where
  ι-ι     : ∀ x y ε → x ≈[ ε ] y → ι x ∼[ ε ] ι y
  ι-lim   : ∀ x y ε δ yc Δ
            → ι x ∼[ ε -₊ δ , Δ ] y δ
            → ι x ∼[ ε ] lim y yc
  lim-ι   : ∀ x y ε δ xc Δ
            → x δ ∼[ ε -₊ δ , Δ ] ι y
            → lim x xc ∼[ ε ] ι y
  lim-lim : ∀ x y ε δ η xc yc Δ
            → x δ ∼[ ε -₊ (δ +₊ η) , Δ ] y η
            → lim x xc ∼[ ε ] lim y yc
  isProp∼ : ∀ x ε y → isProp (x ∼[ ε ] y)
