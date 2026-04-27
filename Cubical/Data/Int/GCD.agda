module Cubical.Data.Int.GCD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Divisibility renaming (_∣_ to _∣ℕ_)
import Cubical.Data.Nat.GCD as ℕ
open import Cubical.Data.Int
open import Cubical.Data.Int.Divisibility

------------------------------------------------------------------------
-- Definition
------------------------------------------------------------------------

gcd : ℤ → ℤ → ℤ
gcd i j = pos (ℕ.gcd  (abs i) (abs j))

gcdSym : ∀ i j → gcd i j ≡ gcd j i
gcdSym i j = cong pos (ℕ.gcdSym (abs i) (abs j))

------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------

gcd[i,j]∣i : ∀ i j → gcd i j ∣ i
gcd[i,j]∣i i j = ∣ℕ→∣ (ℕ.gcd[m,n]∣m (abs i) (abs j))

gcd[i,j]∣j : ∀ i j → gcd i j ∣ j
gcd[i,j]∣j i j = ∣ℕ→∣ (ℕ.gcd[m,n]∣n (abs i) (abs j))

gcd-greatest : ∀ {i j c} → c ∣ i → c ∣ j → c ∣ gcd i j
gcd-greatest ci cj = ∣ℕ→∣ (ℕ.gcd-greatest (∣→∣ℕ ci) (∣→∣ℕ cj))

gcd[0,0]≡0 : gcd 0 0 ≡ 0
gcd[0,0]≡0  = refl

gcd[i,j]≡0⇒i≡0 : ∀ {i j} → gcd i j ≡ 0 → i ≡ 0
gcd[i,j]≡0⇒i≡0 {i} {j} eqn = abs≡0 i (ℕ.gcd[m,n]≡0⇒m≡0 {abs i}{abs j} (injPos eqn))

gcd[i,j]≡0⇒j≡0 : ∀ {i j} → gcd i j ≡ 0 → j ≡ 0
gcd[i,j]≡0⇒j≡0 {i}{j} eqn = gcd[i,j]≡0⇒i≡0 {j}{i} (gcdSym j i ∙ eqn)
