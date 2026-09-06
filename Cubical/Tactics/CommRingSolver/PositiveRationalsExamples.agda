{-
  The rationals solver `ℚ!` on the goals the premetric layer produces:
  literal fractions, positive rationals through `fst`, their halves and
  means, and `max`/`min`. An atom works when it reduces to a fraction on
  representatives; an opaque application such as `f q` does not.
-}
module Cubical.Tactics.CommRingSolver.PositiveRationalsExamples where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals hiding (_+_ ; _·_ ; _-_; -_)
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.NatPlusOne
import Cubical.Data.Int

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open CommRingStr (ℚCommRing .snd)

-- literals
_ : [ 1 / 2 ] + [ 1 / 2 ] ≡ 1
_ = ℚ!

_ : ∀ (x y z : ℚ) → 4 · (([ 1 / 6 ] · x) + (x · [ 1 / 3 ])) + (z · (2 - [ 8 / 4 ])) + y ≡ x + y + x + z - z
_ = λ _ _ _ → ℚ!

-- epsilon bookkeeping
_ : (ε δ η η' a : ℚ) → (ε - (δ + η)) + ((a + δ) + (η' - a)) ≡ (ε + η') - η
_ = λ _ _ _ _ _ → ℚ!

-- positive rationals as atoms, through fst
_ : (ε : ℚ₊) → fst ε + fst ε ≡ 2 · fst ε
_ = λ _ → ℚ!

_ : (ε δ : ℚ₊) (q : ℚ) → [ 1 / 2 ] · fst ε + (q - fst δ) + [ 1 / 2 ] · fst ε ≡ (q + fst ε) - fst δ
_ = λ _ _ _ → ℚ!

-- operations on positive rationals whose rational part reduces by unfolding
_ : (ε δ : ℚ₊) → fst (ε +₊ δ) ≡ fst δ + fst ε
_ = λ _ _ → ℚ!

_ : (ε : ℚ₊) → fst (ε /2₊) + fst (ε /2₊) ≡ fst ε
_ = λ _ → ℚ!

_ : (ε : ℚ₊) → fst (ε /4₊) + fst (ε /4₊) + fst (ε /2₊) ≡ fst ε
_ = λ _ → ℚ!

_ : (ε δ : ℚ₊) → fst (mean₊ ε δ) + fst (mean₊ ε δ) ≡ fst ε + fst δ
_ = λ _ _ → ℚ!

_ : (ε δ : ℚ₊) → fst (max₊ ε δ) + fst ε ≡ fst ε + fst (max₊ ε δ)
_ = λ _ _ → ℚ!

-- max and min on ℚ as atoms
_ : (q r : ℚ) → max q r + q ≡ q + max q r
_ = λ _ _ → ℚ!

_ : (q : ℚ) → max q (- q) - max q (- q) ≡ 0
_ = λ _ → ℚ!

_ : (q r s : ℚ) → min q r · s + max q r · s ≡ s · (max q r + min q r)
_ = λ _ _ _ → ℚ!
