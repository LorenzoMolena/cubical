module Cubical.Algebra.OrderedCommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Equiv
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.QuosetReasoning
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Toset
open import Cubical.Relation.Binary.Order.Loset

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Algebra.OrderedCommRing.Base

private
  variable
    ℓ ℓ' : Level

module OrderedCommRingTheory
  (R : OrderedCommRing ℓ ℓ')
  where

  open BinaryRelation
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

  
  data Trichotomy (x y : ⟨ R ⟩) : Type (ℓ-max ℓ ℓ') where
    lt : x < y → Trichotomy x y
    eq : x ≡ y → Trichotomy x y
    gt : y < x → Trichotomy x y

  IsTrichotomous : Type (ℓ-max ℓ ℓ')
  IsTrichotomous = ∀ x y → Trichotomy x y

  ------------------------------------------------------------------------
  -- 1. Order core (partial / strict order)
  ------------------------------------------------------------------------

  module Trichotomous (_≟_ : IsTrichotomous) where
    cmp-≤ : (x ≤ y) ⊎ (y ≤ x)
    cmp-≤ = {!!}


    ≤-total : (x ≤ y) ⊎ (y ≤ x)
    ≤-total = cmp-≤

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
  module IntegralDomain (is-domain-pos : ∀ x y z → (0r < z) → x · z ≡ y · z → x ≡ y) where
    is-domain-neg : (z < 0r) → x · z ≡ y · z → x ≡ y
    is-domain-neg = {!   !}

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

    ·MonoR≤≃ : 0r < z → (x ≤ y) ≃ (x · z ≤ y · z)
    ·MonoR≤≃ = {!!}

    ·MonoL≤≃ : 0r < z → (x ≤ y) ≃ (z · x ≤ z · y)
    ·MonoL≤≃ = {!!}

    ·MonoR<≃ : 0r < z → (x < y) ≃ (x · z < y · z)
    ·MonoR<≃ = {!!}

    ·MonoL<≃ : 0r < z → (x < y) ≃ (z · x < z · y)
    ·MonoL<≃ = {!!}

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
  -- 6. Min/Max
  ------------------------------------------------------------------------

  ≤maxL : x ≤ max x y
  ≤maxL = {!!}

  ≤maxR : y ≤ max x y
  ≤maxR = {!!}

  lub≤ : x ≤ z → y ≤ z → max x y ≤ z
  lub≤ = {!!}

  ≤minL : min x y ≤ x
  ≤minL = {!!}

  ≤minR : min x y ≤ y
  ≤minR = {!!}

  glb≤ : z ≤ x → z ≤ y → z ≤ min x y
  glb≤ = {!!}

  ------------------------------------------------------------------------
  -- 7. Strict strengthening/weakening utilities
  ------------------------------------------------------------------------

  <→+δ≤ : x < y → Σ[ δ ∈ _ ] ((0r < δ) × (x + δ ≤ y))
  <→+δ≤ = {!!}

  ------------------------------------------------------------------------
  -- 8. Monotone/antitone maps (templates)
  ------------------------------------------------------------------------

  isMonotone≤ : (f : ⟨ R ⟩ → ⟨ R ⟩) → Type (ℓ-max ℓ ℓ')
  isMonotone≤ f = ∀ {x y} → x ≤ y → f x ≤ f y

  isAntitone≤ : (f : ⟨ R ⟩ → ⟨ R ⟩) → Type (ℓ-max ℓ ℓ')
  isAntitone≤ f = ∀ {x y} → x ≤ y → f y ≤ f x

  +isMonotone≤L : ∀ {z} → isMonotone≤ (z +_)
  +isMonotone≤L = {!!}

  +isMonotone≤R : ∀ {z} → isMonotone≤ (_+ z)
  +isMonotone≤R = +MonoR≤ _ _ _

  ·isMonotone≤L : ∀ {z} → 0r ≤ z → isMonotone≤ (z ·_)
  ·isMonotone≤L = {!!}

  ·isMonotone≤R : ∀ {z} → 0r ≤ z → isMonotone≤ (_· z)
  ·isMonotone≤R 0≤z = ·MonoR≤ _ _ _ 0≤z

  negIsAntitone : isAntitone≤ (-_)
  negIsAntitone = {!!}

  ------------------------------------------------------------------------
  -- 9. Comparisons to zero/one
  ------------------------------------------------------------------------

  0≤x,y≤1→x·y≤1 : 0r ≤ x → x ≤ 1r → 0r ≤ y → y ≤ 1r → x · y ≤ 1r
  0≤x,y≤1→x·y≤1 = {!!}

  1≤x,y→1≤x·y : 1r ≤ x → 1r ≤ y → 1r ≤ x · y
  1≤x,y→1≤x·y = {!!}

  ------------------------------------------------------------------------
  -- 10. Convenient equivalences (shift/cancel)
  ------------------------------------------------------------------------

  +MonoR≤≃ : (x ≤ y) ≃ (x + z ≤ y + z)
  +MonoR≤≃ = propBiimpl→Equiv
    (is-prop-valued≤ _ _)
    (is-prop-valued≤ _ _)
    (+MonoR≤ _ _ _)
    +CancelR≤

  +MonoL≤≃ : (x ≤ y) ≃ (z + x ≤ z + y)
  +MonoL≤≃ = {!!}

  +MonoR<≃ : (x < y) ≃ (x + z < y + z)
  +MonoR<≃ = {!!}

  +MonoL<≃ : (x < y) ≃ (z + x < z + y)
  +MonoL<≃ = {!!}

  Connected< : isConnected _<_
  Connected< _ _ (a≮b , b≮a) =
    is-antisym _ _
      (invEq (≤≃¬> _ _) b≮a)
      (invEq (≤≃¬> _ _) a≮b)

  module Decidable< (isDecidable< : isDecidable _<_) where
    TrichotomyisProp : ∀ {x y} → isProp (Trichotomy x y)
    TrichotomyisProp (lt p) (lt q) = cong lt (is-prop-valued< _ _ _ _)
    TrichotomyisProp {y = y} (lt p) (eq q) = ⊥.rec (is-irrefl y (subst (_< y) q p))
    TrichotomyisProp {y = y} (lt p) (gt q) = ⊥.rec (is-irrefl y (is-trans< _ _ _ q p))
    TrichotomyisProp {y = y} (eq p) (lt q) = ⊥.rec (is-irrefl y (subst (_< y) p q))
    TrichotomyisProp (eq p) (eq q) = cong eq (is-set _ _ _ _)
    TrichotomyisProp {x} (eq p) (gt q) = ⊥.rec (is-irrefl x (subst (_< x) (sym p) q))
    TrichotomyisProp {x} (gt p) (lt q) = ⊥.rec (is-irrefl x (is-trans< _ _ _ q p))
    TrichotomyisProp {x} (gt p) (eq q) = ⊥.rec (is-irrefl x (subst (_< x) (sym q) p))
    TrichotomyisProp (gt p) (gt q) = cong gt (is-prop-valued< _ _ _ _)

    _≟_ : IsTrichotomous
    _≟_ = IsTosetReflClosure<→IsTrichotomous
      (isLoset→isTosetReflClosure isLoset isDecidable<)
      where
        isLoset : IsLoset _<_
        isLoset = isloset
          is-set is-prop-valued< is-irrefl is-trans< is-asym is-weakly-linear Connected<

        IsTosetReflClosure<→IsTrichotomous : IsToset (ReflClosure _<_) → IsTrichotomous
        IsTosetReflClosure<→IsTrichotomous torecl x y = ∥₁.rec
          TrichotomyisProp
          (λ { (inl (inl p)) → lt p
             ; (inl (inr p)) → eq p
             ; (inr (inl p)) → gt p
             ; (inr (inr p)) → eq (sym p) })
          (is-total x y)
          where
            open IsToset torecl using (is-total)

  module Discrete (isDiscrete : Discrete ⟨ R ⟩) where
