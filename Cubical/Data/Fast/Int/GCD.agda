{-
  Common-denominator decomposition of fast integers through the gcd on ℕ.

  Kept out of `Cubical.Data.Fast.Int.Properties` because `Cubical.Data.Nat.GCD`
  imports `Cubical.Data.Int.Divisibility`, which uses the commutative ring
  solver, and the solver's generic configuration imports the fast integers.
-}
module Cubical.Data.Fast.Int.GCD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Nat.GCD

open import Cubical.Data.Fast.Int

-- TODO : generalise to Vec and BigOp
sing×[pos]Decompose : (x y : ℤ) → Σ[ (x' , y') ∈ (ℕ × ℕ) ] ((x · y ≡ pos (x' ℕ.· y')) ⊎ (x · y ≡ - pos (x' ℕ.· y')))
sing×[pos]Decompose (pos n) (pos m) = (n , m) , inl refl
sing×[pos]Decompose (pos n) (negsuc m) = (n , suc m) , inr (pos·negsuc n m)
sing×[pos]Decompose (negsuc n) (pos m) = (suc n , m) , inr (negsuc·pos n m)
sing×[pos]Decompose (negsuc n) (negsuc m) = (suc n , suc m) , inl (negsuc·negsuc n m)

gcdℤ : (a b : ℤ) → Σ[ (a' , b' , c ) ∈ _ × _ × _ ]
                (a ≡ a' · pos c) × (b ≡ b' · pos c)
gcdℤ a b =
  let ((a' , p) , (b' , q)) = map-× ∣-untrunc ∣-untrunc (gcdIsGCD (abs a) (abs b) .fst)
  in (sign a · pos a' , sign b · pos b' , (gcd (abs a) (abs b))) ,
       (sym (sign·abs a)
        ∙∙ cong (sign a ·_) (cong pos (sym p))
        ∙∙ ·Assoc _ _ _)
       , sym (sign·abs b)
        ∙∙ cong (sign b ·_) (cong pos (sym q))
        ∙∙ ·Assoc _ _ _
