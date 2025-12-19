{-# OPTIONS --no-exact-split #-}
module Cubical.Data.Fin.Inductive.Literals where

open import Agda.Builtin.Nat
  using (suc)
open import Agda.Builtin.FromNat
  renaming (Number to HasFromNat)
open import Cubical.Data.Fin.Inductive.Base
  using (Fin ; fromℕ<)
open import Cubical.Data.Nat.Order.Inductive
  using (_<ᵗ_)

instance
  fromNatFin : {n : _} → HasFromNat (Fin (suc n))
  fromNatFin {n} = record
    { Constraint = λ m → m <ᵗ (suc n)
    ; fromNat    = λ m ⦃ m<n ⦄ → fromℕ< m n m<n
    }

private
  open import Cubical.Data.Nat
  open import Cubical.Foundations.Prelude
  test₀ : PathP (λ _ → Fin 100003000001) 10000000102 10000000102
  test₀ = refl
