{-
  Support code for the specialised rationals solver, moved here from the
  bottom of `Cubical.Data.Rationals.Order` on Marcin Grzybowski's
  `comm-ring-solver-improvments` branch so that Lorenzo Molena's rationals
  files stay verbatim on this fork. `ℚ₊` is the one every premetric module
  uses, `PositiveRationals.ℚ₊`.
-}
module Cubical.Tactics.CommRingSolver.Specialised.RationalsEqElims where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.List using (List;[];_∷_)
open import Cubical.Data.Nat as ℕ using (ℕ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Fast.Int.Base as ℤ using (ℤ)
import Cubical.Data.Fast.Int.Order as ℤ
import Cubical.Data.Fast.Int.Properties as ℤP

open import Cubical.HITs.SetQuotients

open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order using (_<_; inj)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals using (module PositiveRationals)
open PositiveRationals using (ℚ₊) public

eqℚ : ∀ {k m k' m'} → (k , 1+ m) ∼ (k' , 1+ m') → [ k / 1+ m ] ≡ [ k' / 1+ m' ]
eqℚ = eq/ _ _

module EqElims where
 data ℚTypes : Type where
  [ℚ] [ℚ₊] : ℚTypes

 ℚSignature : Type
 ℚSignature = List ℚTypes

 lrhsDom : ℚTypes → Type
 lrhsDom [ℚ] = ℚ
 lrhsDom [ℚ₊] = ℚ₊


 lrhsDomFst : ℚTypes → Type
 lrhsDomFst [ℚ] = ℤ
 lrhsDomFst [ℚ₊] = ℕ₊₁

 lrhsCtr : ∀ b → lrhsDomFst b → ℕ₊₁ → (lrhsDom b)
 lrhsCtr [ℚ] k m = [ k , m ]
 lrhsCtr [ℚ₊] n m = [ ℕ₊₁→ℤ n , m ] , inj (ℤ.pos<pos tt)

 LRhs : ℚSignature → Type
 LRhs [] = ℚ × ℚ
 LRhs (x ∷ xs) = lrhsDom x → LRhs xs

 LemType : ∀ s → LRhs s → Type
 LemType [] (lhs , rhs) = lhs ≡ rhs
 LemType (x ∷ xs) lrhs = (k : lrhsDomFst x) (m : ℕ₊₁) → LemType xs (lrhs (lrhsCtr x k m))


 EqType : ∀ s → LRhs s → Type
 EqType [] (lhs , rhs) = lhs ≡ rhs
 EqType (x ∷ xs) lrhs = (q : lrhsDom x) → EqType xs (lrhs q)

 isPropEqType : ∀ s → (lrhs : LRhs s) → isProp (EqType s lrhs)
 isPropEqType [] lrhs = isSetℚ _ _
 isPropEqType (_ ∷ s) lrhs = isPropΠ $ isPropEqType s ∘ lrhs

 EllimEqₛ : ∀ s → (lrhs : LRhs s) → LemType s lrhs → EqType s lrhs
 EllimEqₛ [] lrhs e = e
 EllimEqₛ ([ℚ] ∷ xs) lrhs e = ElimProp.go w
  where
  w : ElimProp _
  w .ElimProp.prop = isPropEqType xs ∘ lrhs
  w .ElimProp.fun (k , m) = EllimEqₛ xs (lrhs _) (e k m)

 EllimEqₛ ([ℚ₊] ∷ xs) lrhs e = uncurry (ElimProp.go w)
  where
  w : ElimProp (λ z → ∀ p → EqType xs (lrhs (z , p)))
  w .ElimProp.prop q = isPropΠ λ _ → isPropEqType xs (lrhs (q , _))
  w .ElimProp.fun (ℤ.pos (suc n) , m) (inj (ℤ.pos<pos _)) = EllimEqₛ xs (lrhs _) (e (1+ n) m)

open import Cubical.Data.Empty using (⊥)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals

ℚCommRingIsNotZeroRing : ℚCommRing .snd .CommRingStr.1r ≡ ℚCommRing .snd .CommRingStr.0r → ⊥
ℚCommRingIsNotZeroRing = ℤP.0≢1-ℤ ∘S sym ∘S eq/⁻¹ _ _
