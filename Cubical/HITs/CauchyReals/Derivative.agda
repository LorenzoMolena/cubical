{-# OPTIONS --lossy-unification #-}

module Cubical.HITs.CauchyReals.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv hiding (_■)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

import Cubical.Functions.Logic as L

open import Cubical.Algebra.CommRing.Instances.Int

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Bool.Base using () renaming (Bool to 𝟚 ; true to 1̂ ; false to 0̂)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
open import Cubical.Data.Nat.Order.Recursive as OR
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sigma hiding (Path)
open import Cubical.Data.List as L
open import Cubical.Data.List using () renaming (List to ⟦_⟧)
open import Cubical.Foundations.Interpolate
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Data.Rationals using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Data.NatPlusOne
open import Cubical.Foundations.Path
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Rationals using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Properties as ℚ using (invℚ₊;/2₊;x/2<x;/4₊;invℚ)

open import Cubical.Data.NatPlusOne
open import Cubical.Foundations.Path
open import Cubical.Foundations.CartesianKanOps


import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base


import Cubical.Algebra.CommRing as CR

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence

import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.Ring as RP



-- Rℝ = (CR.CommRing→Ring
--                (_ , CR.commringstr 0 1 _+ᵣ_ _·ᵣ_ -ᵣ_ IsCommRingℝ))
-- -- module CRℝ = ?

-- module 𝐑 = CR.CommRingTheory (_ , CR.commringstr 0 1 _+ᵣ_ _·ᵣ_ -ᵣ_ IsCommRingℝ)
-- module 𝐑' = RP.RingTheory Rℝ


at_limitOf_is_ : (x : ℝ) → (∀ r → x ＃ r → ℝ)  → ℝ → Type
at x limitOf f is L =
  ∀ (ε : ℝ₊) → ∃[ δ ∈ ℝ₊ ]
   (∀ r x＃r → absᵣ (x -ᵣ r) <ᵣ fst δ → absᵣ (L -ᵣ f r x＃r) <ᵣ fst ε)


const-lim : ∀ C x → at x limitOf (λ _ _ → C) is C
const-lim C x ε = ∣ (1 , decℚ<ᵣ?) ,
  (λ r x＃r x₁ → subst (_<ᵣ fst ε) (cong absᵣ (sym (+-ᵣ C))) (snd ε)) ∣₁

id-lim : ∀ x → at x limitOf (λ r _ → r) is x
id-lim x ε = ∣ ε , (λ r x＃r p → p )  ∣₁

_$[_]$_ : {x : ℝ}
        → (∀ r → x ＃ r → ℝ)
        → (ℝ → ℝ → ℝ)
        → (∀ r → x ＃ r → ℝ)
        → (∀ r → x ＃ r → ℝ)
f $[ _op_ ]$ g = λ r x → (f r x) op (g r x)

+-lim : ∀ x f g F G
        → at x limitOf f is F
        → at x limitOf g is G
        → at x limitOf (f $[ _+ᵣ_ ]$ g) is (F +ᵣ G)
+-lim x f g F G fL gL ε =
  PT.map2 (λ (δ , p) (δ' , p') →
       (_ , ℝ₊min δ δ') ,
        λ r x＃r x₁ →
         let u = p r x＃r (isTrans<≤ᵣ _ _ _ x₁ {!min≤ᵣ!})
             u' = p' r x＃r (isTrans<≤ᵣ _ _ _ x₁ {!min≤ᵣ!})
         in {!u!})
    (fL (ε ₊／ᵣ₊ 2))
     (gL (ε ₊／ᵣ₊ 2))

At_limitOf_ : (x : ℝ) → (∀ r → x ＃ r → ℝ) → Type
At x limitOf f = Σ _ (at x limitOf f is_)




differenceAt : (ℝ → ℝ) → ℝ → ∀ h → 0 ＃ h → ℝ
differenceAt f x h 0＃h = (f (x +ᵣ h) -ᵣ f x) ／ᵣ[ h , 0＃h ]


derivativeAt : (ℝ → ℝ) → ℝ → Type
derivativeAt f x = At 0 limitOf (differenceAt f x)

derivativeOf_at_is_ : (ℝ → ℝ) → ℝ → ℝ → Type
derivativeOf f at x is d = at 0 limitOf (differenceAt f x) is d

constDerivative : ∀ C x → derivativeOf (λ _ → C) at x is 0
constDerivative C x =
 subst (at 0 limitOf_is 0)
   (funExt₂ λ r 0＃r → sym (𝐑'.0LeftAnnihilates (invℝ r 0＃r)) ∙
     cong (_·ᵣ (invℝ r 0＃r)) (sym (+-ᵣ _)))
   (const-lim 0 0)

idDerivative : ∀ x → derivativeOf (idfun ℝ) at x is 1
idDerivative x =  subst (at 0 limitOf_is 1)
   (funExt₂ λ r 0＃r → sym (x·invℝ[x] r 0＃r) ∙
    cong (_·ᵣ (invℝ r 0＃r)) (sym (L𝐑.lem--063)))
   (const-lim 1 0)



-- derivative-^ⁿ : ∀ n x →
--    derivativeOf (_^ⁿ (suc n)) at x is (fromNat n ·ᵣ (x ^ⁿ n))
-- derivative-^ⁿ zero x ε = {!!}
-- derivative-^ⁿ (suc n) x ε = {!!}

