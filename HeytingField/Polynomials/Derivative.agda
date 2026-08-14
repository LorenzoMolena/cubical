{-# OPTIONS --safe #-}
module HeytingField.Polynomials.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; separatedℕ; predℕ)
open import Cubical.Data.Nat.Order as ℕOrd
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
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
open import HeytingField.Polynomials.Degree

private module Helpers (R : CommRing ℓ-zero) where
  open CommRingStr (str R)
  interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  interchange a b c d = solve! R

module FieldPolyDerivative (F : HeytingField ℓ-zero ℓ-zero) where
  open FieldTheory F
  open PolyModTheory FCRing
  open PolyMod FCRing using (Poly→Prf; ElimProp; elimProp2; module Elim; isSetPoly) renaming (Poly→Fun to coefficent)
  open Elim renaming (f to Elim)

  -- The symbolic derivative of a polynomial
  diff : Poly FCRing → Poly FCRing
  diff [] = 0P
  -- We know that a ∷ P is a + (X · P), and since a is a constant, its derivative is zero and can be ignored.
  -- so diff (a ∷ P) should be diff (X · P) 
  -- which should be diff X · P + X · diff P by the product rule for differentiation
  -- which reduces to P + 0r ∷ diff P
  diff (a ∷ P) = P Poly+ (0r ∷ diff P)
  diff (drop0 i) = drop0 i

  -- Differentiation is linear
  diff+ : ∀ P Q → diff (P Poly+ Q) ≡ diff P Poly+ diff Q
  diff+ = elimProp2 _ refl (λ r P p → refl) (λ r P p → sym $ Poly+Lid _) (λ r s P Q p →
      (P Poly+ Q) Poly+ (0r ∷ diff (P Poly+ Q))               ≡⟨ cong ((P Poly+ Q) Poly+_) (cong₂ _∷_ (sym (+IdR _)) p) ⟩
      (P Poly+ Q) Poly+ ((0r ∷ diff P) Poly+ (0r ∷ diff Q))   ≡⟨ interchange P Q (0r ∷ diff P) (0r ∷ diff Q) ⟩
      ((P Poly+ (0r ∷ diff P)) Poly+ (Q Poly+ (0r ∷ diff Q))) ∎
    ) (isSetPoly _ _) where open Helpers (UnivariatePolyList FCRing)

  diffConst* : ∀ r P → diff (r PolyConst* P) ≡ r PolyConst* diff P
  diffConst* r = ElimProp _ refl (λ s P p → sym $
      r PolyConst* (P Poly+ (0r ∷ diff P)) ≡⟨ PolyConst*LDistrPoly+ r P (0r ∷ diff P) ⟩
      (r PolyConst* P) Poly+ ((r · 0r) ∷ (r PolyConst* diff P)) ≡⟨ cong ((r PolyConst* P) Poly+_) (cong₂ _∷_ (0RightAnnihilates r) (sym p)) ⟩
      diff (r PolyConst* (s ∷ P)) ∎
    ) (isSetPoly _ _)

  -- -- The product rule
  -- diff* : ∀ P Q → diff (P Poly* Q) ≡ (diff P Poly* Q) Poly+ (P Poly* diff Q)
  -- diff* = elimProp2 _ refl (λ r P p →
  --     diff ((r ∷ P) Poly* 0P)                          ≡⟨ cong diff (0PLeftAnnihilates (r ∷ P)) ⟩
  --     0P                                               ≡⟨ sym (cong₂ _Poly+_ (0PLeftAnnihilates (diff (r ∷ P))) (0PLeftAnnihilates (r ∷ P)) ) ⟩
  --     (diff (r ∷ P) Poly* 0P) Poly+ ((r ∷ P) Poly* 0P) ∎
  --   ) (λ r P p → refl) (λ r s P Q p →
  --     diff (0r ∷ ((r PolyConst* Q) Poly+ (P Poly* (s ∷ Q))))
  --       ≡⟨ cong (diff ∘ (0r ∷_) ∘ ((r PolyConst* Q) Poly+_)) (Poly*Commutative P (s ∷ Q)) ⟩
  --     diff (0r ∷ ((r PolyConst* Q) Poly+ ((s ∷ Q) Poly* P)))
  --       ≡⟨ diff+ (0r ∷ (r PolyConst* Q)) (0r ∷ ((s ∷ Q) Poly* P)) ⟩
  --     diff (0r ∷ (r PolyConst* Q)) Poly+ diff (0r ∷ ((s ∷ Q) Poly* P))
  --       ≡⟨ cong₂ _Poly+_ (diffConst* r (0r ∷ Q)) (diff+ (0r ∷ (s PolyConst* P)) (0r ∷ 0r ∷ (Q Poly* P))) ⟩
  --     (r PolyConst* (diff (0r ∷ Q))) Poly+ (diff (0r ∷ (s PolyConst* P)) Poly+ diff (0r ∷ 0r ∷ Q Poly* P))
  --       ≡⟨ {!!} ⟩
  --     {!!} ∎
  --   ) (isSetPoly _ _)

  
