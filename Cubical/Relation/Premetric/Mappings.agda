module Cubical.Relation.Premetric.Mappings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.NatPlusOne.Base as ℕ₊₁
open import Cubical.Data.Int.Fast.Base as ℤ
open import Cubical.Data.Int.Fast.Properties as ℤ
open import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Rationals.Fast.Base as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚ

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Relation.Premetric.Base

private
  variable
    ℓM ℓM' ℓN ℓN' : Level

module _
  {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A)
  (N : PremetricStr ℓN' B)
  (f : A → B)
  where

  private
    module M = PremetricStr M
    module N = PremetricStr N

  isNonExpanding : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isNonExpanding = ∀ x y ε → x M.≈[ ε ] y → f x N.≈[ ε ] f y

  isPropIsNonExpanding : isProp isNonExpanding
  isPropIsNonExpanding = isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  isLipschitzWith : ℚ₊ → Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isLipschitzWith L = ∀ x y ε → x M.≈[ ε ] y → f x N.≈[ L ·₊ ε ] f y

  isPropIsLipschitzWith : ∀ L → isProp (isLipschitzWith L)
  isPropIsLipschitzWith L = isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  isLipschitz : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isLipschitz = ∃[ L ∈ ℚ₊ ] isLipschitzWith L

  isPropIsLipschitz : isProp isLipschitz
  isPropIsLipschitz = squash₁

  isContinuousAt : (x : A) → Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isContinuousAt x = ∀ ε → ∃[ δ ∈ ℚ₊ ] (∀ y → x M.≈[ δ ] y → f x N.≈[ ε ] f y)

  isPropIsContinuousAt : ∀ x → isProp (isContinuousAt x)
  isPropIsContinuousAt x = isPropΠ λ _ → squash₁

  isContinuous : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isContinuous = ∀ x → isContinuousAt x

  isPropIsContinuous : isProp isContinuous
  isPropIsContinuous = isPropΠ isPropIsContinuousAt

  isUniformlyContinuousWith : (ℚ₊ → ℚ₊) → Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isUniformlyContinuousWith μ = ∀ x y ε → x M.≈[ μ ε ] y → f x N.≈[ ε ] f y

  isPropIsUniformlyContinuousWith : ∀ μ → isProp (isUniformlyContinuousWith μ)
  isPropIsUniformlyContinuousWith μ = isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  isUniformlyContinuous : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isUniformlyContinuous = ∃[ μ ∈ (ℚ₊ → ℚ₊) ] isUniformlyContinuousWith μ

  isPropIsUniformlyContinuous : isProp isUniformlyContinuous
  isPropIsUniformlyContinuous = squash₁

  isSetℚ₊ : isSet ℚ₊
  isSetℚ₊ = isSetΣSndProp ℚ.isSetℚ (ℚ.isProp< 0)

  -- 1/_ : ℚ₊ → ℚ₊
  -- 1/_ = uncurry (SQ.elim
  --   (λ _ → isSetΠ λ _ → isSetℚ₊)
  --   (λ { (pos zero    , 1+ d) p → ⊥.rec (ℤ.isIrrefl< p)
  --      ; (negsuc n    , 1+ d) p → ⊥.rec (ℤ.¬pos≤negsuc p)
  --      ; (pos (suc n) , 1+ d) p → [ pos (suc d) / 1+ n ] , ℤ.zero-<possuc })
  --   λ { (pos zero    , 1+ b) (pos zero    , 1+ d) r → {!   !}
  --     ; (pos zero    , 1+ b) (pos (suc c) , 1+ d) r → {!   !}
  --     ; (pos (suc a) , 1+ b) (pos zero    , 1+ d) r → {!   !}
  --     ; (pos (suc a) , 1+ b) (pos (suc c) , 1+ d) r → {!   !}
  --     ; (pos a    , 1+ b)    (negsuc c , 1+ d)    r → {!   !}
  --     ; (negsuc a , 1+ b)    (pos    c , 1+ d)    r → {!   !}
  --     ; (negsuc a , 1+ b)    (negsuc c , 1+ d)    r → {!   !} } )

  -- isLipschitz→isUniformlyContinuous : isLipschitz → isUniformlyContinuous
  -- isLipschitz→isUniformlyContinuous = {!   !}

C[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
C[ (M , MPr) , (N , NPr) ] = Σ[ f ∈ (M → N) ] isContinuous MPr NPr f

-- infixr 6 _$≈_
-- _$≈_ : {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'}
--     → C[ M , N ] → ⟨ M ⟩ → ⟨ N ⟩
-- _$≈_ = fst

UC[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
UC[ (M , MPr) , (N , NPr) ] = Σ[ f ∈ (M → N) ] isUniformlyContinuous MPr NPr f

record IsPremetricEquiv {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A) (e : A ≃ B) (N : PremetricStr ℓN' B)
  : Type (ℓ-suc (ℓ-max ℓM (ℓ-max ℓN (ℓ-max ℓM' ℓN'))))
  where
  constructor
   ispremetricequiv
  -- Shorter qualified names
  private
    module M = PremetricStr M
    module N = PremetricStr N

  field
    pres≈ : ∀ x y ε → x M.≈[ ε ] y ≃ equivFun e x N.≈[ ε ] equivFun e y
