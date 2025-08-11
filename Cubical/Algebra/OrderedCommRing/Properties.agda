module Cubical.Algebra.OrderedCommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma using (Σ; _,_)

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.QuosetReasoning
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Algebra.OrderedCommRing.Base

private
  variable
    ℓ ℓ' : Level

module OrderedCommRingTheory
  (R : OrderedCommRing ℓ ℓ')
  where

  open OrderedCommRingStr (str R) renaming (_⊓_ to min ; _⊔_ to max)

  open <-≤-Reasoning
    ⟨ R ⟩
    (posetstr _ isPoset)
    (quosetstr _ (isStrictOrder→isQuoset isStrictOrder))
    (λ _ → <-≤-trans _ _ _) (λ _ → ≤-<-trans _ _ _) (<-≤-weaken _ _)
  open <-syntax
  open ≤-syntax
  open ≡-syntax

  private
    variable
      x y z x' y' ε : ⟨ R ⟩

  ------------------------------------------------------------------------
  -- 1. Order core (partial / strict order)
  ------------------------------------------------------------------------

  {-

  // need further assumptions on R

  cmp-≤ : (x ≤ y) ⊎ (y ≤ x)
  cmp-≤ = {!!}


  ≤-total : (x ≤ y) ⊎ (y ≤ x)
  ≤-total = cmp-≤

  -}

  ------------------------------------------------------------------------
  -- 2. Order ↔ equality bridges
  ------------------------------------------------------------------------

  ≤→¬> : (x ≤ y) → ¬ (y < x)
  ≤→¬> = equivFun (≤≃¬> _ _)

  ¬>→≤ : ¬(y < x) → (x ≤ y)
  ¬>→≤ = invEq (≤≃¬> _ _)

  <→≢ : (x < y) → ¬(x ≡ y)
  <→≢ = {!!}

  ------------------------------------------------------------------------
  -- 3. Interaction with addition
  ------------------------------------------------------------------------

  -- 3.1 Monotonicity and cancellation
  +MonoL≤ : x ≤ y → z + x ≤ z + y
  +MonoL≤ {x} {y} {z} x≤y = begin≤
    z + x ≡→≤⟨ +Comm _ _ ⟩
    x + z ≤⟨ +MonoR≤ _ _ _ x≤y ⟩
    y + z ≡→≤⟨ +Comm _ _ ⟩
    z + y ◾

  +MonoL< : x < y → z + x < z + y
  +MonoL< = {!!}

  +CancelL≤ : z + x ≤ z + y → x ≤ y
  +CancelL≤ = {!!}

  +CancelR≤ : x + z ≤ y + z → x ≤ y
  +CancelR≤ = {!!}

  +CancelL< : z + x < z + y → x < y
  +CancelL< = {!!}

  +CancelR< : x + z < y + z → x < y
  +CancelR< = {!!}

  -- 3.2 Zero, negation, subtraction
  0≤1 : 0r ≤ 1r
  0≤1 = <-≤-weaken _ _ 0<1

  -Antitone≤ : x ≤ y → - y ≤ - x
  -Antitone≤ = {!!}

  -Antitone< : x < y → - y < - x
  -Antitone< = {!!}

  ≤≃0≤Δ : (x ≤ y) ≃ (0r ≤ y - x)
  ≤≃0≤Δ = {!!}

  <≃0<Δ : (x < y) ≃ (0r < y - x)
  <≃0<Δ = {!!}

  SubLAntitone≤ : x ≤ y → z - y ≤ z - x
  SubLAntitone≤ = {!!}

  ------------------------------------------------------------------------
  -- 4. Interaction with multiplication
  ------------------------------------------------------------------------

  -- 4.1 Nonnegativity/positivity closure
  0≤· : 0r ≤ x → 0r ≤ y → 0r ≤ x · y
  0≤· = {!!}

  0<· : 0r < x → 0r < y → 0r < x · y
  0<· = {!!}

  {-

  // might need further assumptions on R

  square-nonneg : (0r ≤ (x · x))
  square-nonneg = {!!}

  -}

--  square-pos    : (x ＃ 0r) → (0r < (x · x))
--  square-pos = {!!}

  -- 4.2 Monotonicity (restricted)

  ·MonoL≤ : 0r ≤ z → x ≤ y → z · x ≤ z · y
  ·MonoL≤ = {!!}

  ·MonoL< : 0r < z → x < y → z · x < z · y
  ·MonoL< = {!!}

  -- 4.3 Sign rules for products

  pos·neg→neg : (0r < x) → (y < 0r) → ((x · y) < 0r)
  pos·neg→neg = {!!}

  neg·pos→neg : (x < 0r) → (0r < y) → ((x · y) < 0r)
  neg·pos→neg = {!!}

  neg·neg→pos : (x < 0r) → (y < 0r) → (0r < (x · y))
  neg·neg→pos = {!!}

  nonneg·nonpos→nonpos : (0r ≤ x) → (y ≤ 0r) → ((x · y) ≤ 0r)
  nonneg·nonpos→nonpos = {!!}

  nonpos·nonneg→nonpos : (x ≤ 0r) → (0r ≤ y) → ((x · y) ≤ 0r)
  nonpos·nonneg→nonpos = {!!}

  nonpos·nonpos→nonneg : (x ≤ 0r) → (y ≤ 0r) → ((x · y) ≤ 0r)
  nonpos·nonpos→nonneg = {!!}

  -- 4.4 Cancellation with positive factors
  -- Needs the assumption "nontrivial zero divisors" or similar ones
  module _ (is-domain : ∀ x y z → (0r < z) → x · z ≡ y · z → x ≡ y) where
    ·CancelR≤ : (0r < z) → x · z ≤ y · z → x ≤ y
    ·CancelR≤ = {!!}

    ·CancelL≤ : (0r < z) → z · x ≤ z · y → x ≤ y
    ·CancelL≤ = {!!}

    ·CancelR< : (0r < z) → x · z < y · z → x < y
    ·CancelR< = {!!}

    ·CancelL< : (0r < z) → z · x < z · y → x < y
    ·CancelL< = {!!}

    x≤-x→x≤0 : x ≤ - x → x ≤ 0r
    x≤-x→x≤0 = {!!}

    -x≤x→0≤x : - x ≤ x → 0r ≤ x
    -x≤x→0≤x = {!!}


  -- 4.5 Bounds and unit-ish facts (no inverses assumed)

  0≤x,y≤1→x∙y≤y : 0r ≤ x → x ≤ 1r → 0r ≤ y → y ≤ 1r → x · y ≤ y
  0≤x,y≤1→x∙y≤y = {!!}

  0≤x,y≤1→x∙y≤x : 0r ≤ x → x ≤ 1r → 0r ≤ y → y ≤ 1r → x · y ≤ x
  0≤x,y≤1→x∙y≤x = {!!}

  0≤x,1≤y→x≤x·y : 0r ≤ x → 1r ≤ y → x ≤ x · y
  0≤x,1≤y→x≤x·y = {!!}

  ------------------------------------------------------------------------
  -- 5. Negation & subtraction (sign algebra)
  ------------------------------------------------------------------------

  -Antitone≤≃ : (x ≤ y) ≃ (- y ≤ - x)
  -Antitone≤≃ = {!   !}

  -Antitone<≃ : (x < y) ≃ (- y < - x)
  -Antitone<≃ = {!!}

  ≤0≃0≤- : (x ≤ 0r) ≃ (0r ≤ - x)
  ≤0≃0≤- = {!!}

  0≤≃-≤0 : (0r ≤ x) ≃ (- x ≤ 0r)
  0≤≃-≤0 = {!!}

  ------------------------------------------------------------------------
  -- 7. Min/Max (if provided)
  ------------------------------------------------------------------------

  max-ubˡ : (x ≤ (max x y))
  max-ubˡ = {!!}

  max-ubʳ : (y ≤ (max x y))
  max-ubʳ = {!!}

  max-le : (x ≤ z) → (y ≤ z) → ((max x y) ≤ z)
  max-le = {!!}

  min-lbˡ : ((min x y) ≤ x)
  min-lbˡ = {!!}

  min-lbʳ : ((min x y) ≤ y)
  min-lbʳ = {!!}

  le-min : (z ≤ x) → (z ≤ y) → (z ≤ (min x y))
  le-min = {!!}

  +-mono-≤-max : (x ≤ y) → ((x + z) ≤ (max (y + z) (z + y)))
  +-mono-≤-max = {!!}

  ·-mono-≤-max-nonneg : (0r ≤ z) → (x ≤ y) → ((x · z) ≤ (max (y · z) (z · y)))
  ·-mono-≤-max-nonneg = {!!}

  ------------------------------------------------------------------------
  -- 8. Distributivity and order (derived)
  ------------------------------------------------------------------------

  distrib-≤-left : (0r ≤ x) → ((x · (y + z)) ≤ ((x · y) + (x · z)))
  distrib-≤-left = {!!}

  distrib-≤-right : (0r ≤ x) → (((y + z) · x) ≤ ((y · x) + (z · x)))
  distrib-≤-right = {!!}

  ·-sub-distrˡ-≤-nonneg : (0r ≤ x) → ((x · (y - z)) ≤ ((x · y) - (x · z)))
  ·-sub-distrˡ-≤-nonneg = {!!}

  ·-sub-distrʳ-≤-nonneg : (0r ≤ x) → (((y - z) · x) ≤ ((y · x) - (z · x)))
  ·-sub-distrʳ-≤-nonneg = {!!}

  ------------------------------------------------------------------------
  -- 9. Strict strengthening/weakening utilities
  ------------------------------------------------------------------------

  <→≤-succedent : (x < y) → (x ≤ y)
  <→≤-succedent = {!!}

--  ≤∧＃→<        : (x ≤ y) → (x ＃ y) → (x < y)
--  ≤∧＃→< = {!!}

  <→≤-+ε       : (0r < ε) → (x < y) → ((x + ε) ≤ y)
  <→≤-+ε = {!!}

  ------------------------------------------------------------------------
  -- 10. Monotone/antitone maps (templates)
  ------------------------------------------------------------------------

  Monotoneᵣ : (f : ⟨ R ⟩ → ⟨ R ⟩) → Type (ℓ-max ℓ ℓ')
  Monotoneᵣ f = ∀ {x y} → (x ≤ y) → ((f x) ≤ (f y))

  Antitoneᵣ : (f : ⟨ R ⟩ → ⟨ R ⟩) → Type (ℓ-max ℓ ℓ')
  Antitoneᵣ f = ∀ {x y} → (x ≤ y) → ((f y) ≤ (f x))

  +-mono-functionˡ : (z : ⟨ R ⟩) → Monotoneᵣ (λ x → (z + x))
  +-mono-functionˡ = {!!}

  +-mono-functionʳ : (z : ⟨ R ⟩) → Monotoneᵣ (λ x → (x + z))
  +-mono-functionʳ = {!!}

  ·-mono-functionˡ-nonneg : {z : ⟨ R ⟩} → (0r ≤ z) → Monotoneᵣ (λ x → (z · x))
  ·-mono-functionˡ-nonneg = {!!}

  ·-mono-functionʳ-nonneg : {z : ⟨ R ⟩} → (0r ≤ z) → Monotoneᵣ (λ x → (x · z))
  ·-mono-functionʳ-nonneg = {!!}

  neg-antitone : Antitoneᵣ (λ x → (- x))
  neg-antitone = {!!}

  ------------------------------------------------------------------------
  -- 11. Comparisons to zero/one (grab-bag)
  ------------------------------------------------------------------------

  ≤-0-iff-neg≥0 : ((x ≤ 0r) ≃ (0r ≤ (- x)))
  ≤-0-iff-neg≥0 = {!!}

  0-≤-iff-neg≤0 : ((0r ≤ x) ≃ (((- x) ≤ 0r)))
  0-≤-iff-neg≤0 = {!!}

  1≤-mul-cancelˡ-pos : (0r < y) → (1r ≤ x) → (y ≤ (y · x))
  1≤-mul-cancelˡ-pos = {!!}

  1≤-mul-cancelʳ-pos : (0r < x) → (1r ≤ y) → (x ≤ (x · y))
  1≤-mul-cancelʳ-pos = {!!}

  mul≤-one-when-≤1 : (0r ≤ x) → (x ≤ 1r) → (0r ≤ y) → (y ≤ 1r) → ((x · y) ≤ 1r)
  mul≤-one-when-≤1 = {!!}

  one≤-mul-when-≥1 : (1r ≤ x) → (1r ≤ y) → (1r ≤ (x · y))
  one≤-mul-when-≥1 = {!!}

  ------------------------------------------------------------------------
  -- 12. Convenient equivalences (shift/cancel)
  ------------------------------------------------------------------------

  ≤-shiftˡ-+ : (((x + z) ≤ (y + z)) ≃ (x ≤ y))
  ≤-shiftˡ-+ = {!!}

  ≤-shiftʳ-+ : (((z + x) ≤ (z + y)) ≃ (x ≤ y))
  ≤-shiftʳ-+ = {!!}

  <-shiftˡ-+ : (((x + z) <  (y + z)) ≃ (x <  y))
  <-shiftˡ-+ = {!!}

  <-shiftʳ-+ : (((z + x) <  (z + y)) ≃ (x <  y))
  <-shiftʳ-+ = {!!}

  ≤-shiftˡ-·-pos : (0r < z) → (((x · z) ≤ (y · z)) ≃ (x ≤ y))
  ≤-shiftˡ-·-pos = {!!}

  ≤-shiftʳ-·-pos : (0r < z) → (((z · x) ≤ (z · y)) ≃ (x ≤ y))
  ≤-shiftʳ-·-pos = {!!}

  <-shiftˡ-·-pos : (0r < z) → (((x · z) <  (y · z)) ≃ (x <  y))
  <-shiftˡ-·-pos = {!!}

  <-shiftʳ-·-pos : (0r < z) → (((z · x) <  (z · y)) ≃ (x <  y))
  <-shiftʳ-·-pos = {!!}

  ≤-0-iff-≤-neg : ((x ≤ 0r) ≃ ((x + x) ≤ (0r + x)))
  ≤-0-iff-≤-neg = {!!}
