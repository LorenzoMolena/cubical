module Cubical.Relation.Premetric.MorePremetric.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc) renaming (
  _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _∸_ to _∸ℕ_)
open import Cubical.Data.Nat.Order as ℕ renaming (
  _≤_ to _≤ℕ_ ; _<_ to _<ℕ_)
open import Cubical.Data.NatPlusOne as ℕ₊₁ using (ℕ₊₁ ; 1+_)
open import Cubical.Data.Int.Fast as ℤ using (ℤ ; pos ; negsuc ; _ℕ-_) renaming (
  _+_ to _+ℤ_ ; _·_ to _·ℤ_ ; _-_ to _-ℤ_ ; -_ to -ℤ_ ; abs to ∣_∣ℤ)
open import Cubical.Data.Int.Fast.Order as ℤ using () renaming (
  _≤_ to _≤ℤ_ ; _<_ to _<ℤ_ )

open import Cubical.Data.Rationals.Fast.Base
open import Cubical.Data.Rationals.Fast.Properties as ℚ using () renaming (
  _+_ to _+ℚ_ ; _·_ to _·ℚ_ ; _-_ to _-ℚ_ ; -_ to -ℚ_)
open import Cubical.Data.Rationals.Fast.Order as ℚ using () renaming (
  _≤_ to _≤ℚ_ ; _<_ to _<ℚ_ )

open import Cubical.Tactics.CommRingSolver

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

0<ₚℚ : ℚ → hProp ℓ-zero
0<ₚℚ = SQ.rec isSetHProp (λ
  { (pos zero    , 1+ b)    → ⊥ , isProp⊥
  ; (pos (suc n) , 1+ b) → Unit , λ tt tt → refl
  ; (negsuc n    , 1+ b)    → ⊥ , isProp⊥ })
  λ { (pos zero    , 1+ b) (pos zero    , 1+ d) p → refl
    ; (pos zero    , 1+ b) (pos (suc n) , 1+ d) p → ⊥.rec (ℕ.znots (ℤ.injPos p))
    ; (pos (suc m) , 1+ b) (pos zero    , 1+ d) p → ⊥.rec (ℕ.snotz (ℤ.injPos p))
    ; (pos (suc m) , 1+ b) (pos (suc n) , 1+ d) p → refl
    ; (pos zero    , 1+ b) (negsuc n    , 1+ d) p → refl
    ; (pos (suc m) , 1+ b) (negsuc n    , 1+ d) p → ⊥.rec (ℤ.posNotnegsuc _ _ p)
    ; (negsuc m    , 1+ b) (pos zero    , 1+ d) p → refl
    ; (negsuc m    , 1+ b) (pos (suc n) , 1+ d) p → ⊥.rec (ℤ.negsucNotpos _ _ p)
    ; (negsuc m    , 1+ b) (negsuc n    , 1+ d) p → refl }

0<ℚ : ℚ → Type
0<ℚ = fst ∘ 0<ₚℚ

is-prop-valued-0<ℚ : ∀ x → isProp (0<ℚ x)
is-prop-valued-0<ℚ = snd ∘ 0<ₚℚ

0<ℚ→<ℚ : ∀ x → 0<ℚ x → 0 <ℚ x
0<ℚ→<ℚ = SQ.elimProp (λ x → isProp→ (ℚ.isProp< 0 x))
  λ { (pos (suc n) , (1+ b)) p → n , sym (ℤ.·IdR (pos (suc n))) }

<ℚ→0<ℚ : ∀ x → 0 <ℚ x → 0<ℚ x
<ℚ→0<ℚ = SQ.elimProp (λ x → isProp→ (is-prop-valued-0<ℚ x))
  λ { (pos zero , (1+ b))    → ℤ.isIrrefl<
    ; (pos (suc n) , (1+ b)) → λ _ → tt
    ; (negsuc n , (1+ b))    → ℤ.¬pos≤negsuc }

open Positiveᵗ ℚOrderedCommRing 0<ℚ is-prop-valued-0<ℚ {!   !} {!   !} renaming (
    R₊ to ℚ₊ ; _⊔₊_ to max₊
  ; R₊AdditiveSemigroup to +ℚ₊Semigroup
  ; R₊MultiplicativeCommMonoid to ·ℚ₊CommMonoid) public

private
  variable
    ℓ ℓ' ℓ'' : Level

record IsPremetric {M : Type ℓ}
                        (_≈[_]_ : M → ℚ₊ → M → Type ℓ') : Type (ℓ-max ℓ ℓ') where

  constructor ispremetric

  field
    isSetM        : isSet M
    isProp≈       : ∀ x y ε → isProp (x ≈[ ε ] y)
    isRefl≈       : ∀ x     ε   → x ≈[ ε ] x
    isSym≈        : ∀ x y   ε   → x ≈[ ε ] y → y ≈[ ε ] x
    isSeparated≈  : ∀ x y       → (∀ ε → x ≈[ ε ] y) → x ≡ y
    isTriangular≈ : ∀ x y z ε δ → x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε +₊ δ ] z
    isRounded≈    : ∀ x y   ε   → x ≈[ ε ] y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x ≈[ δ ] y)

unquoteDecl IsPremetricIsoΣ = declareRecordIsoΣ IsPremetricIsoΣ (quote IsPremetric)


record PremetricStr (ℓ' : Level) (M : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  constructor premetricstr

  field
    _≈[_]_      : M → ℚ₊ → M → Type ℓ'
    isPremetric : IsPremetric _≈[_]_

  open IsPremetric isPremetric public

PremetricSpace : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
PremetricSpace ℓ ℓ' = TypeWithStr ℓ (PremetricStr ℓ')

premetricspace : (M : Type ℓ)
                  → (_≈[_]_ : M → ℚ₊ → M → Type ℓ')
                  → IsPremetric _≈[_]_
                  → PremetricSpace ℓ ℓ'
premetricspace M (_≈[_]_) pm = M , (premetricstr _≈[_]_ pm)
