module Cubical.Data.Fast.Int.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat as ℕ hiding (_+_ ; _·_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Base hiding (_ℕ-_ ; _+_ ; _-_ ; _·_ ; sumFinℤ ; sumFinℤId) public
open import Cubical.Data.Fin.Base

infixl 7 _·_
infixl 6 _+_ _-_

ℕ-hlp : ℕ → ℕ → ℤ
ℕ-hlp m-n@zero n-m = - (pos n-m)
ℕ-hlp m-n@(suc _) n-m = pos m-n

_ℕ-_ : ℕ → ℕ → ℤ
m ℕ- n = ℕ-hlp (m ℕ.∸ n) (n ℕ.∸ m)

_+_ : ℤ → ℤ → ℤ
pos m    + pos n    = pos (m ℕ.+ n)
negsuc m + negsuc n = negsuc (suc (m ℕ.+ n))
pos m    + negsuc n = m ℕ- (suc n)
negsuc m + pos n    = n ℕ- (suc m)

_-_ : ℤ → ℤ → ℤ
m - n = m + (- n)

_·_ : ℤ → ℤ → ℤ
pos m       · pos n       = pos (m ℕ.· n)
pos zero    · negsuc n    = pos zero
pos (suc m) · negsuc n    = negsuc (predℕ (suc m ℕ.· suc n))
negsuc m    · pos zero    = pos zero
negsuc m    · pos (suc n) = negsuc (predℕ (suc m ℕ.· suc n))
negsuc m    · negsuc n    = pos (suc m ℕ.· suc n)

sumFinℤ : {n : ℕ} (f : Fin n → ℤ) → ℤ
sumFinℤ {n = n} f = sumFinGen {n = n} _+_ 0 f

sumFinℤId : (n : ℕ) {f g : Fin n → ℤ}
  → ((x : _) → f x ≡ g x) → sumFinℤ {n = n} f ≡ sumFinℤ {n = n} g
sumFinℤId n t i = sumFinℤ {n = n} λ x → t x i

ℕ₊₁→ℤ· : ∀ n m → ℕ₊₁→ℤ ((1+ n) ·₊₁ ((1+ m))) ≡ ℕ₊₁→ℤ (1+ n) · ℕ₊₁→ℤ (1+ m)
ℕ₊₁→ℤ· n m = refl
