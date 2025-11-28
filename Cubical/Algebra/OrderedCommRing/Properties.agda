module Cubical.Algebra.OrderedCommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP using (TypeWithStr)

open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Functions.Logic as L

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Nat as ℕ renaming (
  _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _∸_ to _∸ℕ_ ; _^_ to _^ℕ_)
open import Cubical.Data.Nat.Order as ℕ renaming (
  _≤_ to _≤ℕ_ ; _<_ to _<ℕ_)

open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semiring
open import Cubical.Algebra.Semiring.BigOps
open import Cubical.Algebra.CommSemiring
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Base

open import Cubical.Tactics.CommRingSolver

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Poset hiding (isPseudolattice)
open import Cubical.Relation.Binary.Order.Pseudolattice

open import Cubical.Relation.Binary.Order.QuosetReasoning


private
  variable
    ℓ ℓ' ℓ'' : Level

OrderedCommRing→StrictOrder : OrderedCommRing ℓ ℓ' → StrictOrder ℓ ℓ'
OrderedCommRing→StrictOrder R .fst = R .fst
OrderedCommRing→StrictOrder R .snd = strictorderstr _ isStrictOrder where
  open OrderedCommRingStr (str R)

OrderedCommRing→Ring : OrderedCommRing ℓ ℓ' → Ring ℓ
OrderedCommRing→Ring = CommRing→Ring ∘ OrderedCommRing→CommRing

OrderedCommRing→Poset : OrderedCommRing ℓ ℓ' → Poset ℓ ℓ'
OrderedCommRing→Poset = Pseudolattice→Poset ∘ OrderedCommRing→PseudoLattice

OrderedCommRing→Quoset : OrderedCommRing ℓ ℓ' → Quoset ℓ ℓ'
OrderedCommRing→Quoset = StrictOrder→Quoset ∘ OrderedCommRing→StrictOrder

module _ (R' : OrderedCommRing ℓ ℓ') where
  R = fst R'
  RCR = OrderedCommRing→CommRing R'
  open OrderedCommRingStr (snd R')
  open RingTheory (OrderedCommRing→Ring R')
  open JoinProperties (OrderedCommRing→PseudoLattice R') renaming (
    L≤∨ to L≤⊔ ; R≤∨ to R≤⊔ ; ∨Comm to ⊔Comm ; ∨LUB to ⊔LUB)

  open <-≤-Reasoning R
    (OrderedCommRing→Poset R' .snd)
    (OrderedCommRing→Quoset R' .snd)
    (λ x {y} {z} → <-≤-trans x y z)
    (λ x {y} {z} → ≤-<-trans x y z)
    (λ   {x} {y} → <-≤-weaken x y)
  open <-syntax
  open ≤-syntax
  open ≡-syntax


  module OrderedCommRingTheory where
    open Exponentiation (OrderedCommRing→CommRing R') public

    ≤→¬> : ∀ x y → x ≤ y → ¬ (y < x)
    ≤→¬> x y = equivFun (≤≃¬> x y)

    ¬<→≥ : ∀ x y → ¬ (x < y) → y ≤ x
    ¬<→≥ x y = invEq (≤≃¬> y x)

    abs ∣_∣ : R → R
    abs z = z ⊔ (- z)
    ∣_∣ = abs

    _#_ : R → R → Type ℓ'
    x # y = (x < y) L.⊔′ (y < x)

    +MonoL< : ∀ x y z → x < y → z + x < z + y
    +MonoL< x y z x<y = begin<
      z + x ≡→≤⟨ +Comm z x ⟩ x + z <⟨ +MonoR< x y z x<y ⟩ y + z ≡→≤⟨ +Comm y z ⟩ z + y ◾

    +Mono< : ∀ x y z w → x < y → z < w → x + z < y + w
    +Mono< x y z w x<y z<w = begin<
      x + z <⟨ +MonoR< x y z x<y ⟩ y + z <⟨ +MonoL< z w y z<w ⟩ y + w ◾

    +MonoL≤ : ∀ x y z → x ≤ y → z + x ≤ z + y
    +MonoL≤ x y z x≤y = begin≤
      z + x ≡→≤⟨ +Comm z x ⟩ x + z ≤⟨ +MonoR≤ x y z x≤y ⟩ y + z ≡→≤⟨ +Comm y z ⟩ z + y ◾

    +Mono≤ : ∀ x y z w → x ≤ y → z ≤ w → x + z ≤ y + w
    +Mono≤ x y z w x<y z<w = begin≤
      x + z ≤⟨ +MonoR≤ x y z x<y ⟩ y + z ≤⟨ +MonoL≤ z w y z<w ⟩ y + w ◾

    ·MonoL< : ∀ x y z → 0r < z → x < y → z · x < z · y
    ·MonoL< x y z 0<z x<y = begin<
      z · x ≡→≤⟨ ·Comm z x ⟩ x · z <⟨ ·MonoR< x y z 0<z x<y ⟩ y · z ≡→≤⟨ ·Comm y z ⟩ z · y ◾

    ·MonoL≤ : ∀ x y z → 0r ≤ z → x ≤ y → z · x ≤ z · y
    ·MonoL≤ x y z 0≤z x≤y = begin≤
      z · x ≡→≤⟨ ·Comm z x ⟩ x · z ≤⟨ ·MonoR≤ x y z 0≤z x≤y ⟩ y · z ≡→≤⟨ ·Comm y z ⟩ z · y ◾

    -Flip< : ∀ x y → x < y → - y < - x
    -Flip< x y x<y = begin<
      - y           ≡→≤⟨ solve! RCR ⟩
      x + (- x - y)   <⟨ +MonoR< x y (- x - y) x<y ⟩
      y + (- x - y) ≡→≤⟨ solve! RCR ⟩
      - x             ◾

    ≤abs : ∀ z → z ≤ abs z
    ≤abs z = L≤⊔

    -≤abs : ∀ z → - z ≤ abs z
    -≤abs z = R≤⊔

    #→0<abs : ∀ z → z # 0r → 0r < abs z
    #→0<abs z = PT.rec (is-prop-valued< _ _) λ
      { (inl z<0) → begin<
        0r    ≡→≤⟨ solve! RCR ⟩
        - 0r    <⟨ -Flip< z 0r z<0 ⟩
        - z     ≤⟨ -≤abs _ ⟩
        abs z   ◾
      ; (inr 0<z) → begin<
        0r    <⟨ 0<z ⟩
        z     ≤⟨ ≤abs _ ⟩
        abs z ◾ }

    triangularInequality : ∀ x y → abs (x + y) ≤ abs x + abs y
    triangularInequality x y = ⊔LUB
      (begin≤
        x     + y     ≤⟨ +Mono≤ _ _ _ _ (≤abs x) (≤abs y) ⟩
        abs x + abs y ◾)
      (begin≤
        - (x + y)    ≡→≤⟨ solve! RCR ⟩
        (- x) - y      ≤⟨ +Mono≤ _ _ _ _ (-≤abs x) (-≤abs y) ⟩
        abs x + abs y ◾)

    triangularInequality- : ∀ x y z → abs (x - y) ≤ abs (x - z) + abs (z - y)
    triangularInequality- x y z = begin≤
      abs (x - y)               ≡→≤⟨ cong abs (solve! RCR) ⟩
      abs ((x - z) + (z - y))     ≤⟨ triangularInequality (x - z) (z - y) ⟩
      abs (x - z) + abs (z - y)   ◾

    abs-Comm : ∀ x y → abs (x - y) ≡ abs (y - x)
    abs-Comm x y =
      abs (x - y)             ≡⟨⟩
      (x - y) ⊔ (- (x - y))   ≡⟨ ⊔Comm ⟩
      (- (x - y)) ⊔ (x - y)   ≡⟨ cong₂ _⊔_ (solve! RCR) (solve! RCR) ⟩
      (y - x) ⊔ (- (y - x))   ≡⟨⟩
      abs (y - x)             ∎

  module SumTheory where
    open OrderedCommRingTheory
    open Sum (Ring→Semiring (OrderedCommRing→Ring R')) public

    ∑-syntax : ℕ → (ℕ → R) → R
    ∑-syntax n x = ∑ {suc n} λ k → x (toℕ k)

    syntax ∑-syntax n (λ k → xₖ) = ∑[0 ≤ k ≤ n ] xₖ

    abs∑≤∑abs : ∀ n → (x : ℕ → R) → abs (∑[0 ≤ k ≤ n ] (x k)) ≤ ∑[0 ≤ k ≤ n ] abs (x k)
    abs∑≤∑abs zero    x = flip (subst (abs (x 0 + 0r) ≤_)) (is-refl _) $
      abs (x 0 + 0r) ≡⟨ cong abs (solve! RCR) ⟩
      abs (x 0)      ≡⟨ solve! RCR ⟩
      abs (x 0) + 0r ∎
    abs∑≤∑abs (suc n) x = begin≤
      ∣ x 0 + ∑[0 ≤ k ≤ n ] (x (suc k)) ∣    ≤⟨ triangularInequality (x 0) _ ⟩
      ∣ x 0 ∣ + ∣ ∑[0 ≤ k ≤ n ] (x (suc k)) ∣ ≤⟨ +MonoL≤ _ _ _ (abs∑≤∑abs n (x ∘ suc)) ⟩
      ∑[0 ≤ k ≤ suc n ] ∣ x k ∣              ◾

    geometricSum : ∀ n x → (1r - x) · ∑[0 ≤ k ≤ n ] (x ^ k) ≡ 1r - x ^ (1 +ℕ n)
    geometricSum zero    x = (1r + - x) · (1r + 0r) ≡⟨ solve! RCR ⟩ 1r - (x · 1r) ∎
    geometricSum (suc n) x =
      let
        sₙ = ∑[0 ≤ k ≤ n ] (x ^ k)
        sₙ₊₁ = 1r + ∑[0 ≤ k ≤ n ] (x · (x ^ k))
      in
        (1r - x) · sₙ₊₁                      ≡⟨ step0 ⟩
        (1r - x) · (1r + x · sₙ)             ≡⟨ step1 sₙ ⟩
        (1r - x) + x · ((1r - x) · sₙ)       ≡⟨ step2 ⟩
         1r - x + x · (1r - (x ^ (1 +ℕ n))) ≡⟨ step3 (x ^ (1 +ℕ n)) ⟩
         1r - x ^ (2 +ℕ n)                  ∎
      where
        -- due to the presence of the sum/power term, step1/3 cannot be inlined
        step0 = sym $ cong (((1r - x) ·_) ∘ (1r +_)) (∑Mulrdist {suc n} x ((x ^_) ∘ toℕ))

        step1 : ∀ s → (1r - x) · (1r + x · s) ≡ (1r - x) + x · ((1r - x) · s)
        step1 s = solve! RCR

        step2 = cong ((1r - x +_) ∘ (x ·_)) (geometricSum n x)

        step3 : ∀ p → 1r - x + x · (1r - p) ≡ 1r - x · p
        step3 p = solve! RCR

    0<x<1→x¹⁺ⁿ<1 : ∀ n x → 0r < x → x < 1r → x ^ (1 +ℕ n) < 1r
    0<x<1→x¹⁺ⁿ<1 zero x 0<x x<1 = begin<
      x · 1r ≡→≤⟨ solve! RCR ⟩
      x        <⟨ x<1 ⟩
      1r       ◾
    0<x<1→x¹⁺ⁿ<1 (suc n) x 0<x x<1 = begin<
      x · (x · x ^ n)    <⟨ ·MonoL< _ _ _ 0<x $ 0<x<1→x¹⁺ⁿ<1 n x 0<x x<1 ⟩
      x · 1r           ≡→≤⟨ solve! RCR ⟩
      x                  <⟨ x<1 ⟩
      1r                 ◾

    0<x<1→0<x¹⁺ⁿ : ∀ n x → 0r < x → x < 1r → 0r < x ^ (1 +ℕ n)
    0<x<1→0<x¹⁺ⁿ zero x 0<x x<1 = begin<
      0r        <⟨ 0<x ⟩
      x       ≡→≤⟨ solve! RCR ⟩
      x · 1r    ◾
    0<x<1→0<x¹⁺ⁿ (suc n) x 0<x x<1 = begin<
      0r              ≡→≤⟨ solve! RCR ⟩
      x · 0r            <⟨ ·MonoL< _ _ _ 0<x $ 0<x<1→0<x¹⁺ⁿ n x 0<x x<1 ⟩
      x · (x · x ^ n)   ◾

    GeometricSumPos<1 : ∀ n x → 0r < x → x < 1r
                               → (1r - x) · ∑[0 ≤ k ≤ n ] (x ^ k) ≤ 1r
    GeometricSumPos<1 n x 0<x x<1 = begin≤
      (1r - x) · ∑[0 ≤ k ≤ n ] (x ^ k) ≡→≤⟨ geometricSum n x ∙ sym (+IdR _) ⟩
      1r - x ^ (1 +ℕ n) + 0r             <⟨ +MonoL< _ _ _ (0<x<1→0<x¹⁺ⁿ n x 0<x x<1) ⟩
      1r - x ^ (1 +ℕ n) + x ^ (1 +ℕ n) ≡→≤⟨ lemma (x ^ (1 +ℕ n))  ⟩
      1r                                 ◾
      where
        lemma : ∀ p → (1r - p) + p ≡ 1r
        lemma p = solve! RCR

  module AdditiveSubType
    (P : R → hProp ℓ'')
    (+Closed : (x y : R) → ⟨ P x ⟩ → ⟨ P y ⟩ → ⟨ P (x + y) ⟩)
    where
    open OrderedCommRingTheory

    subtype = Σ[ x ∈ R ] ⟨ P x ⟩

    ι : subtype → R
    ι = fst

    _-subtype_ : subtype → subtype → R
    _-subtype_ x y = ι x - ι y

    _<subtype_ : subtype → subtype → Type ℓ'
    _<subtype_ x y = ι x < ι y

    _≤subtype_ : subtype → subtype → Type ℓ'
    _≤subtype_ x y = ι x ≤ ι y

  module AdditiveAndMultiplicativeSubType
    (P : R → hProp ℓ'')
    (+Closed : (x y : R) → ⟨ P x ⟩ → ⟨ P y ⟩ → ⟨ P (x + y) ⟩)
    (·Closed : (x y : R) → ⟨ P x ⟩ → ⟨ P y ⟩ → ⟨ P (x · y) ⟩)
    where
    open AdditiveSubType P +Closed public

  module Positive where
    open OrderedCommRingTheory
    private
      0<ₚ_ : R → hProp ℓ'
      0<ₚ x = (0r < x) , is-prop-valued< 0r x

      0<+Closed : ∀ x y → 0r < x → 0r < y → 0r < x + y
      0<+Closed x y 0<x 0<y = begin<
        0r       <⟨ 0<x ⟩
        x      ≡→≤⟨ solve! RCR ⟩
        x + 0r   <⟨ +MonoL< 0r y x 0<y ⟩
        x + y    ◾

      0<·Closed : ∀ x y → 0r < x → 0r < y → 0r < x · y
      0<·Closed x y 0<x 0<y = begin<
        0r      ≡→≤⟨ solve! RCR ⟩
        0r · y   <⟨ ·MonoR< 0r x y 0<y 0<x ⟩
        x · y     ◾
    open AdditiveAndMultiplicativeSubType 0<ₚ_ 0<+Closed 0<·Closed renaming (
        subtype to R₊ ; ι to ⟨_⟩₊
      ; _-subtype_ to _-₊_ ; _≤subtype_ to _≤₊_ ; _<subtype_ to _<₊_) public

    R₊≡ = Σ≡Prop (is-prop-valued< 0r)

    _⊔₊_ : R₊ → R₊ → R₊
    (x ⊔₊ y) .fst = ⟨ x ⟩₊ ⊔ ⟨ y ⟩₊
    (x ⊔₊ y) .snd = begin< 0r <⟨ snd x ⟩ ⟨ x ⟩₊ ≤⟨ L≤⊔ ⟩ ⟨ x ⟩₊ ⊔ ⟨ y ⟩₊ ◾

    R₊AdditiveSemigroup : Semigroup _
    fst R₊AdditiveSemigroup = R₊
    SemigroupStr._·_ (snd R₊AdditiveSemigroup) (x , 0<x) (y , 0<y) =
      (x + y , 0<+Closed x y 0<x 0<y)
    SemigroupStr.isSemigroup (snd R₊AdditiveSemigroup) = isSG
      where
        isSG : IsSemigroup _
        isSG .IsSemigroup.is-set = isSetΣSndProp is-set (is-prop-valued< 0r)
        isSG .IsSemigroup.·Assoc = λ _ _ _ → R₊≡ (+Assoc _ _ _)

    open SemigroupStr (snd R₊AdditiveSemigroup) using () renaming (_·_ to _+₊_) public

    R₊MultiplicativeCommMonoid : CommMonoid _
    fst R₊MultiplicativeCommMonoid = R₊
    CommMonoidStr.ε (snd R₊MultiplicativeCommMonoid) = 1r , 0<1
    CommMonoidStr._·_ (snd R₊MultiplicativeCommMonoid) (x , 0<x) (y , 0<y) =
      (x · y , 0<·Closed x y 0<x 0<y)
    CommMonoidStr.isCommMonoid (snd R₊MultiplicativeCommMonoid) =
      makeIsCommMonoid
        (isSetΣSndProp is-set (is-prop-valued< 0r))
        (λ _ _ _ → R₊≡ (·Assoc _ _ _))
        (λ _     → R₊≡ (·IdR _))
        (λ _ _   → R₊≡ (·Comm _ _))

  module NonNegative where
    open OrderedCommRingTheory
    private
      0≤ₚ_ : R → hProp ℓ'
      0≤ₚ x = (0r ≤ x) , is-prop-valued≤ 0r x

      0≤+Closed : ∀ x y → 0r ≤ x → 0r ≤ y → 0r ≤ x + y
      0≤+Closed x y 0≤x 0≤y = begin≤
        0r       ≤⟨ 0≤x ⟩
        x      ≡→≤⟨ solve! RCR ⟩
        x + 0r   ≤⟨ +MonoL≤ 0r y x 0≤y ⟩
        x + y    ◾

      0≤·Closed : ∀ x y → 0r ≤ x → 0r ≤ y → 0r ≤ x · y
      0≤·Closed x y 0≤x 0≤y = begin≤
        0r      ≡→≤⟨ solve! RCR ⟩
        0r · y    ≤⟨ ·MonoR≤ 0r x y 0≤y 0≤x ⟩
        x · y     ◾
    open AdditiveAndMultiplicativeSubType 0≤ₚ_ 0≤+Closed 0≤·Closed renaming (
        subtype to R₀₊ ; ι to ⟨_⟩₀₊
      ; _-subtype_ to _-₀₊_ ; _≤subtype_ to _≤₀₊_ ; _<subtype_ to _<₀₊_) public

    R₀₊≡ = Σ≡Prop (is-prop-valued≤ 0r)

    R₀₊CommSemiring : CommSemiring _
    fst R₀₊CommSemiring = R₀₊
    CommSemiringStr.0r (snd R₀₊CommSemiring) = 0r , is-refl _
    CommSemiringStr.1r (snd R₀₊CommSemiring) = 1r , <-≤-weaken _ _ 0<1
    CommSemiringStr._+_ (snd R₀₊CommSemiring) (x , 0≤x) (y , 0≤y) =
      (x + y , 0≤+Closed x y 0≤x 0≤y)
    CommSemiringStr._·_ (snd R₀₊CommSemiring) (x , 0≤x) (y , 0≤y) =
      (x · y , 0≤·Closed x y 0≤x 0≤y)
    CommSemiringStr.isCommSemiring (snd R₀₊CommSemiring) =
      makeIsCommSemiring
        (isSetΣSndProp is-set (is-prop-valued≤ 0r))
        (λ _ _ _ → R₀₊≡ (+Assoc _ _ _))
        (λ _     → R₀₊≡ (+IdR _))
        (λ _ _   → R₀₊≡ (+Comm _ _))
        (λ _ _ _ → R₀₊≡ (·Assoc _ _ _))
        (λ _     → R₀₊≡ (·IdR _))
        (λ _ _ _ → R₀₊≡ (·DistR+ _ _ _))
        (λ _     → R₀₊≡ (0LeftAnnihilates _))
        (λ _ _   → R₀₊≡ (·Comm _ _))

    R₀₊MultiplicativeCommMonoid : CommMonoid _
    fst R₀₊MultiplicativeCommMonoid = R₀₊
    CommMonoidStr.ε (snd R₀₊MultiplicativeCommMonoid) = 1r , <-≤-weaken _ _ 0<1
    CommMonoidStr._·_ (snd R₀₊MultiplicativeCommMonoid) (x , 0≤x) (y , 0≤y) =
      (x · y , 0≤·Closed x y 0≤x 0≤y)
    CommMonoidStr.isCommMonoid (snd R₀₊MultiplicativeCommMonoid) =
      makeIsCommMonoid
        (isSetΣSndProp is-set (is-prop-valued≤ 0r))
        (λ _ _ _ → R₀₊≡ (·Assoc _ _ _))
        (λ _     → R₀₊≡ (·IdR _))
        (λ _ _   → R₀₊≡ (·Comm _ _))

  private
    2r = 1r + 1r

  module Charactersitic≠2 (1/2 : R) (1/2≡2⁻¹ : 1/2 · 2r ≡ 1r) where
    open OrderedCommRingTheory

    1/2+1/2≡1 : 1/2 + 1/2 ≡ 1r
    1/2+1/2≡1 =
      1/2 + 1/2           ≡⟨ solve! RCR ⟩
      1/2 · 2r            ≡⟨ 1/2≡2⁻¹ ⟩
      1r                  ∎

    0<1/2 : 0r < 1/2
    0<1/2 = flip (PT.rec (is-prop-valued< 0r 1/2))
      (posSum→pos∨pos 1/2 1/2 (subst (0r <_) (sym 1/2+1/2≡1) 0<1)) λ
      { (inl 0<1/2) → 0<1/2
      ; (inr 0<1/2) → 0<1/2
      }

    0≤1/2 : 0r ≤ 1/2
    0≤1/2 = <-≤-weaken _ _ 0<1/2

    mean : R → R → R
    mean x y = (x + y) · 1/2

    meanIdem : ∀ x → mean x x ≡ x
    meanIdem x =
      (x + x) · 1/2     ≡⟨ solve! RCR ⟩
      x · (1/2 + 1/2)   ≡⟨ cong (x ·_) 1/2+1/2≡1 ⟩
      x · 1r            ≡⟨ solve! RCR ⟩
      x                 ∎

    <→<mean : ∀ x y → x < y → x < mean x y
    <→<mean x y x<y = begin<
      x             ≡→≤⟨ sym (meanIdem x) ⟩
      (x + x) · 1/2   <⟨ ·MonoR< (x + x) (x + y) 1/2 0<1/2 (+MonoL< x y x x<y) ⟩
      (x + y) · 1/2   ◾

    <→mean< : ∀ x y → x < y → mean x y < y
    <→mean< x y x<y = begin<
      (x + y) · 1/2   <⟨ ·MonoR< (x + y) (y + y) 1/2 0<1/2 (+MonoR< x y y x<y) ⟩
      (y + y) · 1/2 ≡→≤⟨ meanIdem y ⟩
      y               ◾

    0≤abs : ∀ z → 0r ≤ abs z
    0≤abs z = begin≤
      0r                    ≡→≤⟨ solve! RCR ⟩
      (z - z) · 1/2           ≤⟨ ·MonoR≤ _ _ _ 0≤1/2 $ +Mono≤ _ _ _ _ (≤abs z) (-≤abs z) ⟩
      (abs z + abs z) · 1/2 ≡→≤⟨ meanIdem (abs z) ⟩
      abs z                   ◾
-- -}
