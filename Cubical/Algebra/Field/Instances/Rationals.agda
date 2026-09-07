{-

ℚ is a Field

-}
module Cubical.Algebra.Field.Instances.Rationals where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.Field

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Fast.Int as ℤ
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.SetQuotients as SetQuotients

open import Cubical.Relation.Nullary

open CommRingStr (ℚCommRing .snd)
open Units        ℚCommRing

hasInverseℚ : (x : ℚ) → ¬ x ≡ 0 → Σ[ y ∈ ℚ ] x ℚ.· y ≡ 1
hasInverseℚ = SetQuotients.elimProp
  (λ x → isPropΠ (λ _ → inverseUniqueness x))
  (λ u p → r u p , q u p)
  where
  r : (u : ℤ × ℕ₊₁) → ¬ [ u ] ≡ 0 → ℚ
  r (ℤ.pos zero , b) p =
    Empty.rec (p (numerator0→0 ((ℤ.pos zero , b)) refl))
  r (ℤ.pos (suc n) , b) _ = [ (ℕ₊₁→ℤ b , (1+ n)) ]
  r (ℤ.negsuc n , b) _ = [ (ℤ.- ℕ₊₁→ℤ b , (1+ n)) ]

  q : (u : ℤ × ℕ₊₁) (p : ¬ [ u ] ≡ 0) → [ u ] ℚ.· (r u p) ≡ 1
  q (ℤ.pos zero , b) p =
    Empty.rec (p (numerator0→0 ((ℤ.pos zero , b)) refl))
  q (ℤ.pos (suc n) , (1+ m)) _ =
    eq/ _ _ (ℤ.·IdR _ ∙∙ ℤ.·Comm (pos (suc n)) (pos (suc m)) ∙∙ sym (ℤ.·IdL _))
  q (ℤ.negsuc n , (1+ m)) _ =
    eq/ _ _ (ℤ.·IdR _ ∙∙ ℤ.·Comm (pos (suc n)) (pos (suc m)) ∙∙ sym (ℤ.·IdL _))

0≢1-ℚ : ¬ Path ℚ 0 1
0≢1-ℚ p = 0≢1-ℤ (effective (λ _ _ → isSetℤ _ _) isEquivRel∼ _ _ p)

ℚField : Field ℓ-zero
ℚField = makeFieldFromCommRing ℚCommRing hasInverseℚ 0≢1-ℚ

_[_]⁻¹ : (x : ℚ) → ¬ x ≡ 0 → ℚ
_[_]⁻¹ = FieldStr._[_]⁻¹ $ snd ℚField

_/_[_] : ℚ → (y : ℚ) → ¬ y ≡ 0 → ℚ
x / y [ p ] = x ℚ.· (y [ p ]⁻¹)
