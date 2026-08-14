{-# OPTIONS --allow-unsolved-metas #-}

module HeytingField.Characteristic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Int as ℤ
open import Cubical.Data.Int.Divisibility
open import Cubical.Data.Int.MoreInts.QuoInt as Qℤ using () renaming (ℤ→Int to Qℤ→ℤ; ℤ→IntIsHom· to Qℤ→ℤPres·)
open import Cubical.Data.Rationals.MoreRationals.QuoQ
open import Cubical.Data.Rationals.Base using () renaming (ℕ₊₁→ℤ to ℕ₊₁→ℤ')
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Relation.Nullary

open import HeytingField.Base
open import HeytingField.Properties

open import AntiIdeal
open import IntInitial

private variable
  ℓ ℓ' : Level

module _ (F : HeytingField ℓ ℓ') where
  private module F = FieldTheory F

  open AntiIdeal.AntiIdeal
  open isAntiIdeal
  open Initiality (HeytingField→Ring F) renaming (ℤ→R to ℤ→F; ℤ→RIsHom to ℤ→FIsHom)
  open IsRingHom

  Characteristic : AntiOrder ℓ'
  Characteristic .fst n = ℤ→F n F.# F.0r
  Characteristic .snd .is-prop-valued n = F.is-prop-valued _ _
  Characteristic .snd .+Coclosed m n m+n#0 = F.FieldIs#BinSumLocal _ _ (subst (F._# _) (ℤ→FIsHom .pres+ m n) m+n#0)
  Characteristic .snd .apart0 0#0 = F.is-irrefl F.0r (subst (F._# _) (ℤ→FIsHom .pres0) 0#0)
  Characteristic .snd .·RepelsL m n mn#0 = F.·Cancel#ᵣ _ _ _ $ 
    subst2 F._#_ (ℤ→FIsHom .pres· m n) (sym (F.0LeftAnnihilates (ℤ→F n))) mn#0
  
  hasCharacteristic : ℤ → Type ℓ'
  hasCharacteristic n = ∀ x → Characteristic .fst x ≃ FGAntiOrder {ℓ = ℓ'} n .fst x

  hasCharacteristic' : ℤ → Type (ℓ-suc ℓ')
  hasCharacteristic' n = Characteristic ≡ FGAntiOrder n

  -- The reason for using anti-ideals instead of ideals to define characteristic is so that
  -- a characteristic 0 field contains ℚ

  module Char0 (hasChar0 : hasCharacteristic 0) where
    private
      Qℤ→F = ℤ→F ∘ Qℤ→ℤ
      ℕ₊₁→F = ℤ→F ∘ ℕ₊₁→ℤ'
      Qℤ→FPres· : ∀ x y → Qℤ→F (x Qℤ.· y) ≡ Qℤ→F x F.· Qℤ→F y
      Qℤ→FPres· x y = cong ℤ→F (Qℤ→ℤPres· x y) ∙ ℤ→FIsHom .pres· (Qℤ→ℤ x) (Qℤ→ℤ y)

    ℕ₊₁#0 : ∀ n → ℕ₊₁→F n F.# F.0r
    ℕ₊₁#0 n = invEq (hasChar0 (ℕ₊₁→ℤ' n)) λ 0∣n → lift (encodeℕ _ _ (injPos (∣-zeroˡ 0∣n)))

    ℚ→F : ℚ → ⟨ F ⟩
    ℚ→F = SQ.rec F.is-set (λ (m , n) → Qℤ→F m F.· F.recip _ (ℕ₊₁#0 n)) λ where
      (a , b) (c , d) a/b~c/d →
        F.cross-multiply _ _ _ _ (ℕ₊₁#0 b) (ℕ₊₁#0 d) $
          F.·Comm _ _ ∙ sym (Qℤ→FPres· c (ℕ₊₁→ℤ b)) ∙ cong Qℤ→F (sym a/b~c/d) ∙ Qℤ→FPres· a (ℕ₊₁→ℤ d) ∙ F.·Comm _ _

    ℚ→FCommRingHom : CommRingHom ℚCommRing (HeytingField→CommRing F)
    ℚ→FCommRingHom = ℚ→F , makeIsCommRingHom
      (cong₂ F._·_ (ℤ→FIsHom .pres1) (F.recip≡ _ _ _ (F.·IdR _ ∙ ℤ→FIsHom .pres1)) ∙ F.·IdR _) (
      SQ.elimProp2 (λ _ _ → F.is-set _ _) λ (a , b) (c , d) →
        {!   !}
      ) ({!   !})
  
  module CharP (p : ℤ) (p≠0 : ¬ p ≡ 0) (hasCharP : hasCharacteristic p) where
    -- p must be prime
    -- hasPrimeChar : isPrime p
    -- The cubical library does not have the definition of prime numbers yet 
