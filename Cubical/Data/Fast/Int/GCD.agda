module Cubical.Data.Fast.Int.GCD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Divisibility renaming (_∣_ to _∣ℕ_)
import Cubical.Data.Nat.GCD as ℕ
open import Cubical.Data.Int.GCD public using (
  gcd ; gcdSym ; gcd[i,j]≡0⇒i≡0 ; gcd[i,j]≡0⇒j≡0 ; gcd[0,0]≡0)
open import Cubical.Data.Fast.Int
open import Cubical.Data.Fast.Int.Divisibility

gcd[i,j]∣i : ∀ i j → gcd i j ∣ i
gcd[i,j]∣i i j = ∣ℕ→∣ (ℕ.gcd[m,n]∣m (abs i) (abs j))

gcd[i,j]∣j : ∀ i j → gcd i j ∣ j
gcd[i,j]∣j i j = ∣ℕ→∣ (ℕ.gcd[m,n]∣n (abs i) (abs j))

gcd-greatest : ∀ {i j c} → c ∣ i → c ∣ j → c ∣ gcd i j
gcd-greatest ci cj = ∣ℕ→∣ (ℕ.gcd-greatest (∣→∣ℕ ci) (∣→∣ℕ cj))
