module Cubical.Algebra.OrderedCommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP using (TypeWithStr)

open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Functions.Logic as L

open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semiring
open import Cubical.Algebra.CommSemiring
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Base

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
  open OrderedCommRingStr (snd R')
  open RingTheory (OrderedCommRing→Ring R')
  open JoinProperties (OrderedCommRing→PseudoLattice R') renaming (
    L≤∨ to L≤⊔ ; R≤∨ to R≤⊔ ; ∨LUB to ⊔LUB)

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
    abs : R → R
    abs z = z ⊔ (- z)

    _#_ : R → R → Type ℓ'
    x # y = (x < y) L.⊔′ (y < x)

    +MonoL< : ∀ x y z → x < y → z + x < z + y
    +MonoL< x y z x<y = begin<
      z + x ≡→≤⟨ +Comm z x ⟩ x + z <⟨ +MonoR< x y z x<y ⟩ y + z ≡→≤⟨ +Comm y z ⟩ z + y ◾

    +MonoL≤ : ∀ x y z → x ≤ y → z + x ≤ z + y
    +MonoL≤ x y z x≤y = begin≤
      z + x ≡→≤⟨ +Comm z x ⟩ x + z ≤⟨ +MonoR≤ x y z x≤y ⟩ y + z ≡→≤⟨ +Comm y z ⟩ z + y ◾

    ·MonoL< : ∀ x y z → 0r < z → x < y → z · x < z · y
    ·MonoL< x y z 0<z x<y = begin<
      z · x ≡→≤⟨ ·Comm z x ⟩ x · z <⟨ ·MonoR< x y z 0<z x<y ⟩ y · z ≡→≤⟨ ·Comm y z ⟩ z · y ◾

    ·MonoL≤ : ∀ x y z → 0r ≤ z → x ≤ y → z · x ≤ z · y
    ·MonoL≤ x y z 0≤z x≤y = begin≤
      z · x ≡→≤⟨ ·Comm z x ⟩ x · z ≤⟨ ·MonoR≤ x y z 0≤z x≤y ⟩ y · z ≡→≤⟨ ·Comm y z ⟩ z · y ◾

    -Flip< : ∀ x y → x < y → - y < - x
    -Flip< x y x<y = begin<
      - y           ≡→≤⟨ sym $ +Assoc _ _ _ ∙∙ cong (_- y) (+InvR x) ∙∙ +IdL (- y)  ⟩
      x + (- x - y)   <⟨ +MonoR< x y (- x - y) x<y ⟩
      y + (- x - y) ≡→≤⟨ +Assoc-comm1 _ _ _ ∙∙ cong (- x +_) (+InvR y) ∙∙ +IdR (- x) ⟩
      - x             ◾

    ≤abs : ∀ z → z ≤ abs z
    ≤abs z = L≤⊔

    -≤abs : ∀ z → - z ≤ abs z
    -≤abs z = R≤⊔

    #→0<abs : ∀ z → z # 0r → 0r < abs z
    #→0<abs z = PT.rec (is-prop-valued< _ _) λ
      { (inl z<0) → begin<
        0r   ≡→≤⟨ sym 0Selfinverse ⟩
        - 0r   <⟨ -Flip< z 0r z<0 ⟩
        - z    ≤⟨ -≤abs _ ⟩
        abs z ◾
      ; (inr 0<z) → begin<
        0r      <⟨ 0<z ⟩
        z      ≤⟨ ≤abs _ ⟩
        abs z ◾ }

    triangularInequality : ∀ x y → abs (x + y) ≤ abs x + abs y
    triangularInequality x y = ⊔LUB
      (begin≤
        x     + y     ≤⟨ +MonoR≤ _ _ _ (≤abs x) ⟩
        abs x + y     ≤⟨ +MonoL≤ _ _ _ (≤abs y) ⟩
        abs x + abs y ◾)
      (begin≤
        - (x + y)    ≡→≤⟨ sym $ -Dist x y ⟩
        (- x) - y      ≤⟨ +MonoR≤ _ _ _ (-≤abs x) ⟩
        abs x + (- y)  ≤⟨ +MonoL≤ _ _ _ (-≤abs y) ⟩
        abs x + abs y ◾)

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
        x      ≡→≤⟨ sym $ +IdR x ⟩
        x + 0r   <⟨ +MonoL< 0r y x 0<y ⟩
        x + y    ◾

      0<·Closed : ∀ x y → 0r < x → 0r < y → 0r < x · y
      0<·Closed x y 0<x 0<y = begin<
        0r      ≡→≤⟨ sym $ 0LeftAnnihilates y ⟩
        0r · y   <⟨ ·MonoR< 0r x y 0<y 0<x ⟩
        x · y     ◾
    open AdditiveAndMultiplicativeSubType 0<ₚ_ 0<+Closed 0<·Closed renaming (
        subtype to R₊ ; ι to ⟨_⟩₊
      ; _-subtype_ to _-₊_ ; _≤subtype_ to _≤₊_ ; _<subtype_ to _<₊_) public

    R₀≡ = Σ≡Prop (is-prop-valued< 0r)

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
        isSG .IsSemigroup.·Assoc = λ _ _ _ → R₀≡ (+Assoc _ _ _)

    open SemigroupStr (snd R₊AdditiveSemigroup) using () renaming (_·_ to _+₊_) public

    R₊MultiplicativeCommMonoid : CommMonoid _
    fst R₊MultiplicativeCommMonoid = R₊
    CommMonoidStr.ε (snd R₊MultiplicativeCommMonoid) = 1r , 0<1
    CommMonoidStr._·_ (snd R₊MultiplicativeCommMonoid) (x , 0<x) (y , 0<y) =
      (x · y , 0<·Closed x y 0<x 0<y)
    CommMonoidStr.isCommMonoid (snd R₊MultiplicativeCommMonoid) =
      makeIsCommMonoid
        (isSetΣSndProp is-set (is-prop-valued< 0r))
        (λ _ _ _ → R₀≡ (·Assoc _ _ _))
        (λ _     → R₀≡ (·IdR _))
        (λ _ _   → R₀≡ (·Comm _ _))

  module NonNegative where
    open OrderedCommRingTheory
    private
      0≤ₚ_ : R → hProp ℓ'
      0≤ₚ x = (0r ≤ x) , is-prop-valued≤ 0r x

      0≤+Closed : ∀ x y → 0r ≤ x → 0r ≤ y → 0r ≤ x + y
      0≤+Closed x y 0≤x 0≤y = begin≤
        0r       ≤⟨ 0≤x ⟩
        x      ≡→≤⟨ sym $ +IdR x ⟩
        x + 0r   ≤⟨ +MonoL≤ 0r y x 0≤y ⟩
        x + y    ◾

      0≤·Closed : ∀ x y → 0r ≤ x → 0r ≤ y → 0r ≤ x · y
      0≤·Closed x y 0≤x 0≤y = begin≤
        0r      ≡→≤⟨ sym $ 0LeftAnnihilates y ⟩
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
