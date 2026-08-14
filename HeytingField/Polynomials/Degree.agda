{-# OPTIONS --safe #-}
-- Basic properties of polynomials over Heyting fields

module HeytingField.Polynomials.Degree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; separatedℕ; predℕ)
open import Cubical.Data.Nat.Order as ℕOrd hiding (_≤_; _<_)
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

open import HeytingField.Extension.Base

private variable
  ℓ ℓ' : Level

-- The type of degrees are the bounded upper naturals; classically equivalent to the natural numbers
-- https://www.davidjaz.com/Talks/MHOTT-myers-slides-II.pdf
-- The definitions in the library are currently insufficiently polymorphic,
-- so we have to reduce the generality a bit for now
Deg≤+ : OrderedCommMonoid (ℓ-suc ℓ-zero) ℓ-zero
Deg≤+ = BoundedPropCompletion ℕ≤+

Deg≤· : OrderedCommMonoid (ℓ-suc ℓ-zero) ℓ-zero
Deg≤· = BoundedPropCompletion ℕ≤·

Deg = ⟨ Deg≤+ ⟩

ℕ→Deg : ℕ → Deg
ℕ→Deg n = n ^↑ , isBounded^ n where open PropCompletion _ ℕ≤+

module Deg where
  open OrderedCommMonoidStr (str Deg≤+) renaming (ε to 0d; _·_ to _+_) public
  open OrderedCommMonoidStr (str Deg≤·) using (_·_) renaming (ε to 1d) public

  degsuc : Deg → Deg
  degsuc d .fst .fst zero = ⊥ , isProp⊥
  degsuc d .fst .fst (suc n) = d .fst .fst n
  degsuc d .fst .snd zero m n≤m ()
  degsuc d .fst .snd (suc n) zero n≤m _ = ¬-<-zero n≤m
  degsuc d .fst .snd (suc n) (suc m) n≤m = d .fst .snd n m (pred-≤-pred n≤m)
  degsuc d .snd = PT.map (λ (m , dm) → suc m , dm) (d .snd)

  _<_ : Deg → Deg → Type
  d₁ < d₂ = degsuc d₁ ≤ d₂

open ℕOrd

-- -- Later this will be generalized

--   -- The above is exactly the data we need to define:
--   deg : Poly FCRing → Deg
--   deg P .fst .fst n .fst = P hasDeg≤ n
--   deg P .fst .fst n .snd = isPropHasDeg≤ P n
--   deg P .fst .snd = hasDeg≤trans P
--   deg P .snd = hasSomeDeg≤ P

--   deg+ : Poly FCRing → Deg
--   deg+ P .fst .fst n .fst = P hasDeg< n
--   deg+ P .fst .fst n .snd = isPropHasDeg< P n
--   deg+ P .fst .snd = hasDeg<≤trans P
--   deg+ P .snd = hasSomeDeg< P
