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

open import Cubical.Data.Rationals.Fast.Base as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚ using () renaming (
  _+_ to _+ℚ_ ; _·_ to _·ℚ_ ; _-_ to _-ℚ_ ; -_ to -ℚ_)
open import Cubical.Data.Rationals.Fast.Order as ℚ using () renaming (
  _≤_ to _≤ℚ_ ; _<_ to _<ℚ_ )

-- open import Cubical.Tactics.CommRingSolver

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit as ⊤
open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

private
  variable
    ℓ ℓ' : Level

module ℚ₊ where

  0ℤ<ᵗ_ : ℤ → hProp ℓ-zero
  0ℤ<ᵗ_ (pos zero)    = ⊥    , isProp⊥
  0ℤ<ᵗ_ (pos (suc n)) = Unit , isPropUnit
  0ℤ<ᵗ_ (negsuc n)    = ⊥    , isProp⊥

  0ℤ<ᵗ→≡possuc : ∀ x → fst (0ℤ<ᵗ x) → Σ[ k ∈ ℕ ] x ≡ pos (suc k)
  0ℤ<ᵗ→≡possuc (pos (suc n)) t = n , refl

  onFractions : ℤ × ℕ₊₁ → hProp ℓ-zero
  onFractions = 0ℤ<ᵗ_ ∘ fst

  respect∼ : ∀ x y → x ℚ.∼ y → onFractions x ≡ onFractions y
  respect∼ (pos zero    , 1+ b) (pos zero    , 1+ d) = λ _ → refl
  respect∼ (pos zero    , 1+ b) (pos (suc c) , 1+ d) = ⊥.rec ∘ ℕ.znots ∘ ℤ.injPos
  respect∼ (pos (suc a) , 1+ b) (pos zero    , 1+ d) = ⊥.rec ∘ ℕ.snotz ∘ ℤ.injPos
  respect∼ (pos (suc a) , 1+ b) (pos (suc c) , 1+ d) = λ _ → refl
  respect∼ (pos a       , 1+ b) (negsuc c    , 1+ d) = ⊥.rec ∘ ℤ.posNotnegsuc _ _
  respect∼ (negsuc a    , 1+ b) (pos c       , 1+ d) = ⊥.rec ∘ ℤ.negsucNotpos _ _
  respect∼ (negsuc a    , 1+ b) (negsuc c    , 1+ d) = λ _ → refl

  0<ₚ : ℚ → hProp ℓ-zero
  0<ₚ = SQ.rec isSetHProp onFractions respect∼

  0<ᵗ_ = fst ∘ 0<ₚ

  isProp0<ᵗ : ∀ x → isProp (0<ᵗ x)
  isProp0<ᵗ = snd ∘ 0<ₚ

  0<ᵗ→< : ∀ x → 0<ᵗ x → 0 <ℚ x
  0<ᵗ→< = SQ.elimProp (λ x → isProp→ (ℚ.isProp< 0 x))
    λ { (pos (suc n) , (1+ b)) p → n , sym (ℤ.·IdR (pos (suc n))) }

  <→0<ᵗ : ∀ x → 0 <ℚ x → 0<ᵗ x
  <→0<ᵗ = SQ.elimProp (λ x → isProp→ (isProp0<ᵗ x))
    λ { (pos zero    , 1+ b) → ℤ.isIrrefl<
      ; (pos (suc n) , 1+ b) → λ _ → tt
      ; (negsuc n    , 1+ b) → ℤ.¬pos≤negsuc }

open Positiveᵗ ℚOrderedCommRing
  ℚ₊.0<ᵗ_ ℚ₊.isProp0<ᵗ (λ {x} → ℚ₊.0<ᵗ→< x) (λ {x} → ℚ₊.<→0<ᵗ x) renaming (
    R₊ to ℚ₊ ; _⊔₊_ to max₊
  ; R₊AdditiveSemigroup to +ℚ₊Semigroup
  ; R₊MultiplicativeCommMonoid to ·ℚ₊CommMonoid) public

record IsPremetric {M : Type ℓ} (_≈[_]_ : M → ℚ₊ → M → Type ℓ') : Type (ℓ-max ℓ ℓ') where

  constructor ispremetric

  field
    isSetM        : isSet M
    isProp≈       : ∀ x y ε → isProp (x ≈[ ε ] y)
    isRefl≈       : ∀ x     ε   → x ≈[ ε ] x
    isSym≈        : ∀ x y   ε   → x ≈[ ε ] y → y ≈[ ε ] x
    isSeparated≈  : ∀ x y       → (∀ ε → x ≈[ ε ] y) → x ≡ y
    isTriangular≈ : ∀ x y z ε δ → x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε +₊ δ ] z
    isRounded≈    : ∀ x y   ε   → x ≈[ ε ] y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x ≈[ δ ] y)

record PremetricStr (ℓ' : Level) (M : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  constructor premetricstr

  field
    _≈[_]_      : M → ℚ₊ → M → Type ℓ'
    isPremetric : IsPremetric _≈[_]_

  open IsPremetric isPremetric public

PremetricSpace : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
PremetricSpace ℓ ℓ' = TypeWithStr ℓ (PremetricStr ℓ')
