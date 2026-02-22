module Cubical.Algebra.OrderedCommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP using (TypeWithStr)
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Functions.Logic as L

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Nat as ℕ renaming (
  _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _∸_ to _∸ℕ_ ; _^_ to _^ℕ_)
open import Cubical.Data.Nat.Order as ℕ renaming (
  _≤_ to _≤ℕ_ ; _<_ to _<ℕ_)

open import Cubical.Data.Fast.Int as ℤ using (ℤ ; pos ; negsuc ; _ℕ-_) renaming (
  _+_ to _+ℤ_ ; _·_ to _·ℤ_ ; _-_ to _-ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Fast.Int.Order as ℤ renaming (
  _≤_ to _≤ℤ_ ; _<_ to _<ℤ_ ) hiding (
    0≤→abs≡id ; 0<→abs≡id ; ≤→0≤Δ ; <→0<Δ ; 0≤Δ→≤ ; 0<Δ→<)

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
open import Cubical.Algebra.OrderedCommRing.Instances.Fast.Int

open import Cubical.Tactics.CommRingSolver

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Apartness
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

OrderedCommRing→Apartness : OrderedCommRing ℓ ℓ' → Apartness ℓ ℓ'
OrderedCommRing→Apartness = StrictOrder→Apartness ∘ OrderedCommRing→StrictOrder

module OrderedCommRingReasoning (R' : OrderedCommRing ℓ ℓ') where
  open OrderedCommRingStr (snd R')
  open <-≤-Reasoning
    (fst R')
    (str (OrderedCommRing→Poset  R'))
    (str (OrderedCommRing→Quoset R'))
    (λ x {y} {z} → <-≤-trans x y z)
    (λ x {y} {z} → ≤-<-trans x y z)
    (λ   {x} {y} → <-≤-weaken x y)
    public

  open <-syntax public
  open ≤-syntax public
  open ≡-syntax public


module _ (R' : OrderedCommRing ℓ ℓ') where
  private
    R = fst R'
    RCR = OrderedCommRing→CommRing R'
  open OrderedCommRingStr (snd R')
  open RingTheory (OrderedCommRing→Ring R')
  open PseudolatticeTheory (OrderedCommRing→PseudoLattice R') renaming (
      L≤∨ to L≤⊔ ; R≤∨ to R≤⊔ ; ∨Comm to ⊔Comm ; ∨Idem to ⊔Idem ; ∨LUB to ⊔LUB
    ; ∧≤L to ⊓≤L ; ∧≤R to ⊓≤R ; ∧Comm to ⊓Comm ; ∧Idem to ⊓Idem ; ∧GLB to ⊓GLB)

  open OrderedCommRingReasoning R'

  module OrderedCommRingTheory where
    open Exponentiation (OrderedCommRing→CommRing R') public
    open BinaryRelation

    open ApartnessStr (str (OrderedCommRing→Apartness R')) using (_#_) public

    ≤→¬> : ∀ x y → x ≤ y → ¬ (y < x)
    ≤→¬> x y = equivFun (≤≃¬> x y)

    ¬<→≥ : ∀ x y → ¬ (x < y) → y ≤ x
    ¬<→≥ x y = invEq (≤≃¬> y x)

    ≥Using< : ∀ x y → (x < y → y ≤ x) → y ≤ x
    ≥Using< _ _ <→≥ = ¬<→≥ _ _ (∘diag (≤→¬> _ _ ∘ <→≥))

    abs ∣_∣ : R → R
    abs z = z ⊔ (- z)
    ∣_∣ = abs

    +MonoL< : ∀ x y z → x < y → z + x < z + y
    +MonoL< x y z = subst2 _<_ (+Comm _ _) (+Comm _ _) ∘ +MonoR< x y z

    +Mono< : ∀ x y z w → x < y → z < w → x + z < y + w
    +Mono< x y z w x<y z<w = begin<
      x + z <⟨ +MonoR< x y z x<y ⟩ y + z <⟨ +MonoL< z w y z<w ⟩ y + w ◾

    +MonoL≤ : ∀ x y z → x ≤ y → z + x ≤ z + y
    +MonoL≤ x y z = subst2 _≤_ (+Comm _ _) (+Comm _ _) ∘ +MonoR≤ x y z

    +Mono≤ : ∀ x y z w → x ≤ y → z ≤ w → x + z ≤ y + w
    +Mono≤ x y z w x<y z<w = begin≤
      x + z ≤⟨ +MonoR≤ x y z x<y ⟩ y + z ≤⟨ +MonoL≤ z w y z<w ⟩ y + w ◾

    ·MonoL< : ∀ x y z → 0r < z → x < y → z · x < z · y
    ·MonoL< x y z 0<z x<y = begin<
      z · x ≡→≤⟨ ·Comm z x ⟩ x · z <⟨ ·MonoR< x y z 0<z x<y ⟩ y · z ≡→≤⟨ ·Comm y z ⟩ z · y ◾

    ·MonoL≤ : ∀ x y z → 0r ≤ z → x ≤ y → z · x ≤ z · y
    ·MonoL≤ x y z 0≤z x≤y = begin≤
      z · x ≡→≤⟨ ·Comm z x ⟩ x · z ≤⟨ ·MonoR≤ x y z 0≤z x≤y ⟩ y · z ≡→≤⟨ ·Comm y z ⟩ z · y ◾

    ·CancelL≤ : ∀ x y z → 0r < z → z · x ≤ z · y → x ≤ y
    ·CancelL≤ x y z 0<z zx≤zy = ¬<→≥ y x $ ≤→¬> _ _ zx≤zy ∘ ·MonoL< _ _ z 0<z

    ·CancelR≤ : ∀ x y z → 0r < z → x · z ≤ y · z → x ≤ y
    ·CancelR≤ x y z 0<z zx≤zy = ¬<→≥ y x $ ≤→¬> _ _ zx≤zy ∘ ·MonoR< _ _ z 0<z

    -- NOTE:
    -- These properties don't seems like to be derivable.
    -- However we can prove their double negations, so they are classically valid
    -- Moreover, in a Ordered Heyting Field (where elements are invertible iff they
    -- are apart form zero) we can prove them by multiplying by z⁻¹
    --
    -- ·CancelL< : ∀ x y z → 0r < z → z · x < z · y → x < y
    -- ·CancelL< = ?
    --
    -- ·CancelL< : ∀ x y z → 0r < z → x · z < y · z → x < y
    -- ·CancelL< = ?

    -- These are intended to be used in the order reasoning
    [_]+<_ : ∀ {x y} z → x < y → z + x < z + y
    [_]+<_ z x<y = +MonoL< _ _ z x<y

    _<+[_] : ∀ {x y} → x < y → ∀ z → x + z < y + z
    _<+[_] x<y z = +MonoR< _ _ z x<y

    [_]+≤_ : ∀ {x y} z → x ≤ y → z + x ≤ z + y
    [_]+≤_ z x≤y = +MonoL≤ _ _ z x≤y

    _≤+[_] : ∀ {x y} → x ≤ y → ∀ z → x + z ≤ y + z
    _≤+[_] x≤y z = +MonoR≤ _ _ z x≤y

    [_,_]·<_ : ∀ {x y} z → 0r < z → x < y → z · x < z · y
    [_,_]·<_ z 0<z x<y = ·MonoL< _ _ z 0<z x<y

    _<·[_,_] : ∀ {x y} → x < y → ∀ z → 0r < z → x · z < y · z
    _<·[_,_] x<y z 0<z = ·MonoR< _ _ z 0<z x<y

    [_,_]·≤_ : ∀ {x y} z → 0r ≤ z → x ≤ y → z · x ≤ z · y
    [_,_]·≤_ z 0≤z x≤y = ·MonoL≤ _ _ z 0≤z x≤y

    _≤·[_,_] : ∀ {x y} → x ≤ y → ∀ z → 0r ≤ z → x · z ≤ y · z
    _≤·[_,_] x≤y z 0≤z = ·MonoR≤ _ _ z 0≤z x≤y

    private
      example : ∀ a b c d e f g
              → (0r < f) → a < (b + c) → b ≤ d → (d + c) < (e · f) → e < g
              → a < (g · f)
      example a b c d e f g 0<f a<b+c b≤d d+c<e·f e<g = begin<
        a     <⟨ a<b+c ⟩
        b + c ≤⟨ b≤d ≤+[ c ] ⟩
        d + c <⟨ d+c<e·f ⟩
        e · f <⟨ e<g <·[ f , 0<f ] ⟩
        g · f ◾

    -Flip< : ∀ x y → x < y → - y < - x
    -Flip< x y x<y = begin<
      - y           ≡→≤⟨ solve! RCR ⟩
      x + (- x - y)   <⟨ +MonoR< x y (- x - y) x<y ⟩
      y + (- x - y) ≡→≤⟨ solve! RCR ⟩
      - x             ◾

    -Flip≤ : ∀ x y → x ≤ y → - y ≤ - x
    -Flip≤ x y x≤y = begin≤
      - y           ≡→≤⟨ solve! RCR ⟩
      x + (- x - y)   ≤⟨ +MonoR≤ x y (- x - y) x≤y ⟩
      y + (- x - y) ≡→≤⟨ solve! RCR ⟩
      - x             ◾

    0<→-<0 : ∀ x → 0r < x → - x < 0r
    0<→-<0 x = subst (- x <_) (solve! RCR) ∘ -Flip< 0r x

    <0→0<- : ∀ x → x < 0r → 0r < - x
    <0→0<- x = subst (_< - x) (solve! RCR) ∘ -Flip< x 0r

    0≤→-≤0 : ∀ x → 0r ≤ x → - x ≤ 0r
    0≤→-≤0 x = subst (- x ≤_) (solve! RCR) ∘ -Flip≤ 0r x

    ≤0→0≤- : ∀ x → x ≤ 0r → 0r ≤ - x
    ≤0→0≤- x = subst (_≤ - x) (solve! RCR) ∘ -Flip≤ x 0r

    <→0<Δ : ∀ x y → x < y → 0r < y - x
    <→0<Δ x y x<y = begin< 0r ≡→≤⟨ solve! RCR ⟩ x - x <⟨ +MonoR< _ _ _ x<y ⟩ y - x ◾

    ≤→0≤Δ : ∀ x y → x ≤ y → 0r ≤ y - x
    ≤→0≤Δ x y x≤y = begin≤ 0r ≡→≤⟨ solve! RCR ⟩ x - x ≤⟨ +MonoR≤ _ _ _ x≤y ⟩ y - x ◾

    0<Δ→< : ∀ x y → 0r < y - x → x < y
    0<Δ→< x y 0<y-x = subst2 _<_ (solve! RCR) (solve! RCR) (+MonoR< _ _ x 0<y-x)

    0≤Δ→≤ : ∀ x y → 0r ≤ y - x → x ≤ y
    0≤Δ→≤ x y 0≤y-x = subst2 _≤_ (solve! RCR) (solve! RCR) (+MonoR≤ _ _ x 0≤y-x)

    0≤² : ∀ x → 0r ≤ x · x
    0≤² x = ≥Using< (x · x) 0r λ x²<0 →
      let
        0≤x : 0r ≤ x
        0≤x = ¬<→≥ x 0r λ x<0 → is-irrefl 0r $ begin<
          0r             ≡→≤⟨ sym $ 0LeftAnnihilates (- x) ⟩
          0r · (- x)       <⟨ ∘diag (·MonoR< _ _ _) (<0→0<- x x<0) ⟩
          (- x) · (- x)  ≡→≤⟨ solve! RCR ⟩
          x · x            <⟨ x²<0 ⟩
          0r               ◾
      in
        subst (_≤ x · x) (solve! RCR) (∘diag (·MonoR≤ _ _ _) 0≤x)

    #→0<² : ∀ x → x # 0r → 0r < x · x
    #→0<² x (inl x<0) =
      subst2 _<_ (solve! RCR) (solve! RCR) (∘diag (·MonoR< _ _ _) (<0→0<- x x<0))
    #→0<² x (inr 0<x) =
      subst (_< x · x) (solve! RCR) (∘diag (·MonoR< _ _ _) 0<x)

    ≤abs : ∀ z → z ≤ abs z
    ≤abs z = L≤⊔

    -≤abs : ∀ z → - z ≤ abs z
    -≤abs z = R≤⊔

    0≤abs : ∀ z → 0r ≤ abs z
    0≤abs z = ¬<→≥ (abs z) 0r λ ∣z∣<0 → is-irrefl 0r $ begin<
      0r      ≡→≤⟨ solve! RCR ⟩
      - 0r      <⟨ -Flip< _ _ ∣z∣<0 ⟩
      - abs z   ≤⟨ -Flip≤ _ _ (≤abs z) ⟩
      - z       ≤⟨ -≤abs z ⟩
      abs z     <⟨ ∣z∣<0 ⟩
      0r        ◾

    abs≤0→≡0 : ∀ z → abs z ≤ 0r → z ≡ 0r
    abs≤0→≡0 z ∣z∣≤0 = is-antisym z 0r
      (begin≤
        z     ≤⟨ ≤abs z ⟩
        abs z ≤⟨ ∣z∣≤0 ⟩
        0r         ◾)
      (begin≤
        0r        ≡→≤⟨ solve! RCR ⟩
        - 0r        ≤⟨ -Flip≤ _ _ ∣z∣≤0 ⟩
        - (abs z)   ≤⟨ -Flip≤ _ _ $ -≤abs z ⟩
        - - z     ≡→≤⟨ solve! RCR ⟩
        z           ◾)

    #→0<abs : ∀ z → z # 0r → 0r < abs z
    #→0<abs z (inl z<0) = begin<
      0r    ≡→≤⟨ solve! RCR ⟩
      - 0r    <⟨ -Flip< z 0r z<0 ⟩
      - z     ≤⟨ -≤abs _ ⟩
      abs z   ◾
    #→0<abs z (inr 0<z) = begin<
      0r    <⟨ 0<z ⟩
      z     ≤⟨ ≤abs _ ⟩
      abs z ◾

    abs- : ∀ x → abs (- x) ≡ abs x
    abs- x =
      abs (- x)       ≡⟨⟩
      (- x) ⊔ (- - x) ≡⟨ cong ((- x) ⊔_) (solve! RCR) ⟩
      (- x) ⊔ x       ≡⟨ ⊔Comm ⟩
      x ⊔ (- x)       ≡⟨⟩
      abs x           ∎

    0≤→abs≡id : ∀ x → 0r ≤ x → abs x ≡ x
    0≤→abs≡id x 0≤x = is-antisym (abs x) x
      (⊔LUB (is-refl x) (begin≤ - x ≤⟨ 0≤→-≤0 x 0≤x ⟩ 0r ≤⟨ 0≤x ⟩ x ◾))
      (≤abs x)

    ≤0→abs≡- : ∀ x → x ≤ 0r → abs x ≡ - x
    ≤0→abs≡- x x≤0 = sym (abs- x) ∙ 0≤→abs≡id (- x) (≤0→0≤- x x≤0)

    0<→abs≡id : ∀ x → 0r < x → abs x ≡ x
    0<→abs≡id x = 0≤→abs≡id x ∘ <-≤-weaken 0r x

    <0→abs≡- : ∀ x → x < 0r → abs x ≡ - x
    <0→abs≡- x = ≤0→abs≡- x ∘ <-≤-weaken x 0r

    abs²≡² : ∀ x → abs x · abs x ≡ x · x
    abs²≡² x = is-antisym (abs x · abs x) (x · x)
      (¬<→≥ (x · x) (abs x · abs x) λ x²<∣x∣² →
        let
          0≤x : 0r ≤ x
          0≤x = ¬<→≥ x 0r λ x<0 → is-irrefl (x · x) (begin<
            x · x           <⟨ x²<∣x∣² ⟩
            abs x · abs x ≡→≤⟨ cong (∘diag _·_) (<0→abs≡- x x<0) ∙ solve! RCR ⟩
            x · x           ◾)
        in
          is-irrefl (x · x) (begin<
            x · x           <⟨ x²<∣x∣² ⟩
            abs x · abs x ≡→≤⟨ cong (∘diag _·_) (0≤→abs≡id x 0≤x) ⟩
            x · x           ◾))
      (0≤Δ→≤ (x · x) (abs x · abs x) (begin≤
        0r                          ≡→≤⟨ solve! RCR ⟩
        0r · (abs x - - x)            ≤⟨ ·MonoR≤ 0r _ _ (≤→0≤Δ _ _ (-≤abs x))
                                                        (≤→0≤Δ _ _ (≤abs x)) ⟩
        (abs x - x) · (abs x - - x) ≡→≤⟨ solve! RCR ⟩
        abs x · abs x - x · x         ◾))

    abs²≡²' : ∀ x → abs(x · x) ≡ x · x
    abs²≡²' x = 0≤→abs≡id (x · x) (0≤² x)

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

    abs0 : abs 0r ≡ 0r
    abs0 = 0≤→abs≡id 0r (is-refl 0r)

    abs1 : abs 1r ≡ 1r
    abs1 = 0≤→abs≡id 1r (<-≤-weaken 0r 1r 0<1)

{- TO DO: simplify this construction
  module CanonicalEmbeddings where
    open OrderedCommRingTheory

    ℕ→⟨R⟩ : ℕ → R
    ℕ→⟨R⟩ zero          = 0r
    ℕ→⟨R⟩ one           = 1r
    ℕ→⟨R⟩ (suc (suc n)) = 1r + ℕ→⟨R⟩ (suc n)

    ℤ→⟨R⟩ : ℤ → R
    ℤ→⟨R⟩ (pos n)    = ℕ→⟨R⟩ n
    ℤ→⟨R⟩ (negsuc n) = - ℕ→⟨R⟩ (suc n)

    private
      ℕ→⟨R⟩suc : ∀ x → ℕ→⟨R⟩ (suc x) ≡ 1r + ℕ→⟨R⟩ x
      ℕ→⟨R⟩suc zero    = solve! RCR
      ℕ→⟨R⟩suc (suc x) = refl

      ℕ→⟨R⟩pres+ : ∀ x y → ℕ→⟨R⟩ (x +ℕ y) ≡ ℕ→⟨R⟩ x + ℕ→⟨R⟩ y
      ℕ→⟨R⟩pres+ zero          n       = solve! RCR
      ℕ→⟨R⟩pres+ one           zero    = solve! RCR
      ℕ→⟨R⟩pres+ one           (suc n) = refl
      ℕ→⟨R⟩pres+ (suc (suc m)) n       = cong (1r +_) (ℕ→⟨R⟩pres+ (suc m) n) ∙ solve! RCR

      ℕ→⟨R⟩pres· : ∀ x y → ℕ→⟨R⟩ (x ·ℕ y) ≡ ℕ→⟨R⟩ x · ℕ→⟨R⟩ y
      ℕ→⟨R⟩pres· zero          n = solve! RCR
      ℕ→⟨R⟩pres· one           n = cong ℕ→⟨R⟩ (ℕ.+-zero n) ∙ solve! RCR
      ℕ→⟨R⟩pres· (suc (suc m)) n =
        ℕ→⟨R⟩ (n +ℕ (n +ℕ m ·ℕ n))         ≡⟨ ℕ→⟨R⟩pres+ n (n +ℕ m ·ℕ n) ⟩
        ℕ→⟨R⟩ n + ℕ→⟨R⟩ (n +ℕ m ·ℕ n)       ≡⟨ cong (ℕ→⟨R⟩ n +_) $ ℕ→⟨R⟩pres+ n (m ·ℕ n) ⟩
        ℕ→⟨R⟩ n + (ℕ→⟨R⟩ n + ℕ→⟨R⟩ (m ·ℕ n)) ≡⟨ solve! RCR ⟩
        ℕ→⟨R⟩ n + ℕ→⟨R⟩ n + ℕ→⟨R⟩ (m ·ℕ n)   ≡⟨ cong (_ +_) $ ℕ→⟨R⟩pres· m n ⟩
        ℕ→⟨R⟩ n + ℕ→⟨R⟩ n + ℕ→⟨R⟩ m · ℕ→⟨R⟩ n ≡⟨ solve! RCR ⟩
        (1r + (1r + ℕ→⟨R⟩ m)) · ℕ→⟨R⟩ n      ≡⟨ sym $ cong ((_· ℕ→⟨R⟩ n) ∘ (1r +_)) (ℕ→⟨R⟩suc m) ⟩
        ℕ→⟨R⟩ (suc (suc m)) · ℕ→⟨R⟩ n        ∎

      0<ℕ→⟨R⟩∘suc : ∀ n → 0r < ℕ→⟨R⟩ (suc n)
      0<ℕ→⟨R⟩∘suc zero    = 0<1
      0<ℕ→⟨R⟩∘suc (suc n) = begin<
        0r               ≡→≤⟨ solve! RCR ⟩
        0r + 0r            <⟨ +MonoR< _ _ _ 0<1 ⟩
        1r + 0r            <⟨ +MonoL< _ _ _ (0<ℕ→⟨R⟩∘suc n) ⟩
        1r + ℕ→⟨R⟩ (suc n) ◾

      0≤ℕ→⟨R⟩ : ∀ n → 0r ≤ ℕ→⟨R⟩ n
      0≤ℕ→⟨R⟩ zero    = is-refl 0r
      0≤ℕ→⟨R⟩ (suc n) = <-≤-weaken _ _ (0<ℕ→⟨R⟩∘suc n)

      ℤ→⟨R⟩presℕ- : ∀ x y → ℤ→⟨R⟩ (x ℕ- y) ≡ ℕ→⟨R⟩ x - ℕ→⟨R⟩ y
      ℤ→⟨R⟩presℕ- zero          zero          = solve! RCR
      ℤ→⟨R⟩presℕ- zero          (suc y)       = solve! RCR
      ℤ→⟨R⟩presℕ- (suc x)       zero          = solve! RCR
      ℤ→⟨R⟩presℕ- one           one           = solve! RCR
      ℤ→⟨R⟩presℕ- one           (suc (suc y)) = solve! RCR
      ℤ→⟨R⟩presℕ- (suc (suc x)) one           = solve! RCR
      ℤ→⟨R⟩presℕ- (suc (suc x)) (suc (suc y)) =
        ℤ→⟨R⟩ (suc x ℕ- suc y)                    ≡⟨ ℤ→⟨R⟩presℕ- (suc x) (suc y) ⟩
        ℕ→⟨R⟩ (suc x) - ℕ→⟨R⟩ (suc y)             ≡⟨ solve! RCR ⟩
        1r + ℕ→⟨R⟩ (suc x) - (1r + ℕ→⟨R⟩ (suc y)) ∎

      ℤ→⟨R⟩pres+ : ∀ x y → ℤ→⟨R⟩ (x +ℤ y) ≡ ℤ→⟨R⟩ x + ℤ→⟨R⟩ y
      ℤ→⟨R⟩pres+ (pos m)    (pos n)          = ℕ→⟨R⟩pres+ m n
      ℤ→⟨R⟩pres+ (pos m)    (negsuc n)       = ℤ→⟨R⟩presℕ- m (suc n)
      ℤ→⟨R⟩pres+ (negsuc m) (pos n)          = ℤ→⟨R⟩presℕ- n (suc m) ∙ solve! RCR
      ℤ→⟨R⟩pres+ (negsuc m) (negsuc zero)    =
        - (1r + ℕ→⟨R⟩ (suc (m +ℕ 0))) ≡⟨ cong (-_ ∘ (1r +_) ∘ ℕ→⟨R⟩) $ ℕ.+-zero (suc m) ⟩
        - (1r + ℕ→⟨R⟩ (suc m))        ≡⟨ solve! RCR ⟩
        - ℕ→⟨R⟩ (suc m) - 1r          ∎
      ℤ→⟨R⟩pres+ (negsuc m) (negsuc (suc n)) =
        - (1r + ℕ→⟨R⟩ (suc m +ℕ suc n))         ≡⟨ cong (-_ ∘ (1r +_)) $ ℕ→⟨R⟩pres+ (suc m) _ ⟩
        - (1r + (ℕ→⟨R⟩ (suc m) + ℕ→⟨R⟩ (suc n))) ≡⟨ solve! RCR ⟩
        - ℕ→⟨R⟩ (suc m) - (1r + ℕ→⟨R⟩ (suc n))   ∎

      ℤ→⟨R⟩pres· : ∀ x y → ℤ→⟨R⟩ (x ·ℤ y) ≡ ℤ→⟨R⟩ x · ℤ→⟨R⟩ y
      ℤ→⟨R⟩pres· (pos m)    (pos n)       = ℕ→⟨R⟩pres· m n
      ℤ→⟨R⟩pres· (pos zero) (negsuc n)    = solve! RCR
      ℤ→⟨R⟩pres· (pos (suc m)) (negsuc n) =
        - ℕ→⟨R⟩ (suc m ·ℕ suc n)         ≡⟨ cong -_ (ℕ→⟨R⟩pres· (suc m) (suc n)) ⟩
        - (ℕ→⟨R⟩ (suc m) · ℕ→⟨R⟩ (suc n)) ≡⟨ solve! RCR ⟩
        ℕ→⟨R⟩ (suc m) · - ℕ→⟨R⟩ (suc n)   ∎
      ℤ→⟨R⟩pres· (negsuc m) (pos zero)    = solve! RCR
      ℤ→⟨R⟩pres· (negsuc m) (pos (suc n)) =
        - ℕ→⟨R⟩ (suc m ·ℕ suc n)         ≡⟨ cong -_ (ℕ→⟨R⟩pres· (suc m) (suc n)) ⟩
        - (ℕ→⟨R⟩ (suc m) · ℕ→⟨R⟩ (suc n)) ≡⟨ solve! RCR ⟩
        - ℕ→⟨R⟩ (suc m) · ℕ→⟨R⟩ (suc n)   ∎
      ℤ→⟨R⟩pres· (negsuc m) (negsuc n)    =
        ℕ→⟨R⟩ (suc m ·ℕ suc n)           ≡⟨ ℕ→⟨R⟩pres· (suc m) (suc n) ⟩
        ℕ→⟨R⟩ (suc m) · ℕ→⟨R⟩ (suc n)     ≡⟨ solve! RCR ⟩
        - ℕ→⟨R⟩ (suc m) · - ℕ→⟨R⟩ (suc n) ∎

      ℤ→⟨R⟩pres< : ∀ x y → x <ℤ y → ℤ→⟨R⟩ x < ℤ→⟨R⟩ y
      ℤ→⟨R⟩pres< x y (k , p) = begin<
        ℤ→⟨R⟩ x                      ≡→≤⟨ solve! RCR ⟩
        ℤ→⟨R⟩ x + 0r                   <⟨ +MonoL< _ _ _ (0<ℕ→⟨R⟩∘suc k) ⟩
        ℤ→⟨R⟩ x + ℤ→⟨R⟩ (pos (suc k)) ≡→≤⟨ _ ≡⟨ sym (ℤ→⟨R⟩pres+ x (pos (suc k))) ⟩
        ℤ→⟨R⟩ (x +ℤ pos (suc k))       ≡⟨ sym $ cong ℤ→⟨R⟩ (ℤ.+sucℤ x (pos k)) ⟩
        ℤ→⟨R⟩ (ℤ.sucℤ (x +ℤ pos k))    ≡⟨ cong ℤ→⟨R⟩ (ℤ.sucℤ+ x (pos k)) ⟩
        ℤ→⟨R⟩ (ℤ.sucℤ x +ℤ pos k)      ≡⟨ cong ℤ→⟨R⟩ p ⟩ refl ⟩
        ℤ→⟨R⟩ y                        ◾

      ℤ→⟨R⟩pres≤ : ∀ x y → x ≤ℤ y → ℤ→⟨R⟩ x ≤ ℤ→⟨R⟩ y
      ℤ→⟨R⟩pres≤ x y (k , p) = begin≤
        ℤ→⟨R⟩ x                ≡→≤⟨ solve! RCR ⟩
        ℤ→⟨R⟩ x + 0r             ≤⟨ +MonoL≤ _ _ _ (0≤ℕ→⟨R⟩ k) ⟩
        ℤ→⟨R⟩ x + ℤ→⟨R⟩ (pos k) ≡→≤⟨ sym (ℤ→⟨R⟩pres+ x (pos k)) ∙ cong ℤ→⟨R⟩ p ⟩
        ℤ→⟨R⟩ y                  ◾

      ℤ→⟨R⟩reflect< : ∀ x y → ℤ→⟨R⟩ x < ℤ→⟨R⟩ y → x <ℤ y
      ℤ→⟨R⟩reflect< x y ιx<ιy with x ℤ.≟ y
      ... | lt x<y = x<y
      ... | eq x≡y = ⊥.rec (is-irrefl _ $ subst (_< ℤ→⟨R⟩ y) (cong ℤ→⟨R⟩ x≡y) ιx<ιy)
      ... | gt x>y = ⊥.rec (is-asym _ _ ιx<ιy (ℤ→⟨R⟩pres< y x x>y))

    ℤ→⟨R⟩Hom : IsOrderedCommRingHom (str ℤOrderedCommRing) ℤ→⟨R⟩ (str R')
    ℤ→⟨R⟩Hom = makeIsOrderedCommRingHom
      refl ℤ→⟨R⟩pres+ ℤ→⟨R⟩pres· ℤ→⟨R⟩pres≤ ℤ→⟨R⟩reflect<

    ℤ→⟨R⟩Mono : IsOrderedCommRingMono (str ℤOrderedCommRing) ℤ→⟨R⟩ (str R')
    ℤ→⟨R⟩Mono = makeIsOrderedCommRingMono
      refl ℤ→⟨R⟩pres+ ℤ→⟨R⟩pres· ℤ→⟨R⟩pres≤ ℤ→⟨R⟩pres< ℤ→⟨R⟩reflect<

    ℤOCR→R : OrderedCommRingHom ℤOrderedCommRing R'
    fst ℤOCR→R = ℤ→⟨R⟩
    snd ℤOCR→R = ℤ→⟨R⟩Hom

    ℤOCR↣R : OrderedCommRingMono ℤOrderedCommRing R'
    fst ℤOCR↣R = ℤ→⟨R⟩
    snd ℤOCR↣R = ℤ→⟨R⟩Mono

    isContrHom[ℤ,OCR] : isContr (OrderedCommRingHom ℤOrderedCommRing R')
    fst isContrHom[ℤ,OCR] = ℤOCR→R
    snd isContrHom[ℤ,OCR] (φ , φocrhom) = OrderedCommRingHom≡ λ i n → ℤ→⟨R⟩≡⟨φ⟩ n i
      where
        open IsOrderedCommRingHom φocrhom

        ℕ→⟨R⟩≡⟨φ⟩ : ∀ n → ℕ→⟨R⟩ n ≡ φ (pos n)
        ℕ→⟨R⟩≡⟨φ⟩ zero          = sym pres0
        ℕ→⟨R⟩≡⟨φ⟩ one           = sym pres1
        ℕ→⟨R⟩≡⟨φ⟩ (suc (suc n)) =
          1r  + ℕ→⟨R⟩ (suc n)   ≡⟨ cong (1r +_) (ℕ→⟨R⟩≡⟨φ⟩ (suc n)) ⟩
          1r  + φ (pos (suc n)) ≡⟨ sym $ cong (_+ φ (pos (suc n))) pres1 ⟩
          φ 1 + φ (pos (suc n)) ≡⟨ sym $ pres+ 1 (pos (suc n)) ⟩
          φ (pos (suc (suc n))) ∎

        ℤ→⟨R⟩≡⟨φ⟩ : ∀ n → ℤ→⟨R⟩ n ≡ φ n
        ℤ→⟨R⟩≡⟨φ⟩ (pos n)    = ℕ→⟨R⟩≡⟨φ⟩ n
        ℤ→⟨R⟩≡⟨φ⟩ (negsuc n) = cong -_ (ℕ→⟨R⟩≡⟨φ⟩ (suc n)) ∙ sym (pres- (pos (suc n)))

    isContrℤ↣OCR : isContr (ℤOrderedCommRing ↣ R')
    fst isContrℤ↣OCR = ℤOCR↣R
    snd isContrℤ↣OCR (φ , φocrmono) =
      let
        φocrhom = isOrderedCommRingMono→isOrderedCommRingHom φocrmono
        ℤ→⟨R⟩≡φ = cong fst $ snd isContrHom[ℤ,OCR] (φ , φocrhom)
      in
        OrderedCommRingMono≡ ℤ→⟨R⟩≡φ

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
-}

  module AdditiveSubType
    (P : R → Type ℓ'')
    (P-prop : ∀ x → isProp (P x))
    (+Closed : (x y : R) → P x → P y → P (x + y))
    where
    open OrderedCommRingTheory

    subtype = Σ[ x ∈ R ] P x

    isSetSubtype : isSet subtype
    isSetSubtype = isSetΣSndProp is-set P-prop

    ι : subtype → R
    ι = fst

    subtype≡ : ∀ {x y} → ι x ≡ ι y → x ≡ y
    subtype≡ = Σ≡Prop P-prop

    _+subtype_ : subtype → subtype → subtype
    (x +subtype y) .fst = fst x + fst y
    (x +subtype y) .snd = +Closed (fst x) (fst y) (snd x) (snd y)

    _-subtype_ : subtype → subtype → R
    _-subtype_ x y = ι x - ι y

    _<subtype_ : subtype → subtype → Type ℓ'
    _<subtype_ x y = ι x < ι y

    _≤subtype_ : subtype → subtype → Type ℓ'
    _≤subtype_ x y = ι x ≤ ι y

    infixl 6 _+subtype_ _-subtype_
    infix  4 _<subtype_ _≤subtype_

  module AdditiveAndMultiplicativeSubType
    (P : R → Type ℓ'')
    (P-prop : ∀ x → isProp (P x))
    (+Closed : (x y : R) → P x → P y → P (x + y))
    (·Closed : (x y : R) → P x → P y → P (x · y))
    where
    open AdditiveSubType P P-prop +Closed public

    _·subtype_ : subtype → subtype → subtype
    (x ·subtype y) .fst = fst x · fst y
    (x ·subtype y) .snd = ·Closed (fst x) (fst y) (snd x) (snd y)

    infixl 7 _·subtype_

  -- Of course +Closed and ·Closed are derivable, but for concrete instances
  -- (like the rationals) it's more efficient to use alternative proofs
  module Positive
    (0<+Closed : (x y : R) → 0r < x → 0r < y → 0r < x + y)
    (0<·Closed : (x y : R) → 0r < x → 0r < y → 0r < x · y)
    where

    open AdditiveAndMultiplicativeSubType
      (0r <_) (is-prop-valued< 0r) 0<+Closed 0<·Closed public renaming (
        subtype to R₊ ; isSetSubtype to isSetR₊ ; ι to ⟨_⟩₊ ; subtype≡ to R₊≡
      ; _+subtype_ to _+₊_ ; _·subtype_ to _·₊_ ; _-subtype_ to _-₊_
      ; _≤subtype_ to _≤₊_ ; _<subtype_ to _<₊_)

    open OrderedCommRingTheory

    R₊AdditiveSemigroup : Semigroup _
    fst R₊AdditiveSemigroup = R₊
    SemigroupStr._·_ (snd R₊AdditiveSemigroup) = _+₊_
    SemigroupStr.isSemigroup (snd R₊AdditiveSemigroup) = isSG
      where
        isSG : IsSemigroup _
        isSG .IsSemigroup.is-set = isSetR₊
        isSG .IsSemigroup.·Assoc = λ _ _ _ → R₊≡ (+Assoc _ _ _)

    open SemigroupStr (snd R₊AdditiveSemigroup) public hiding (_·_) renaming (
      ·Assoc to +₊Assoc)

    R₊MultiplicativeCommMonoid : CommMonoid _
    fst R₊MultiplicativeCommMonoid = R₊
    CommMonoidStr.ε   (snd R₊MultiplicativeCommMonoid) = 1r , 0<1
    CommMonoidStr._·_ (snd R₊MultiplicativeCommMonoid) = _·₊_
    CommMonoidStr.isCommMonoid (snd R₊MultiplicativeCommMonoid) =
      makeIsCommMonoid
        isSetR₊
        (λ _ _ _ → R₊≡ (·Assoc _ _ _))
        (λ _     → R₊≡ (·IdR _))
        (λ _ _   → R₊≡ (·Comm _ _))

    open CommMonoidStr (snd R₊MultiplicativeCommMonoid) public hiding (_·_) renaming (
      ε to 1₊ ; ·Assoc to ·₊Assoc ; ·IdR to ·₊IdR ; ·Comm to ·₊Comm)

    selfSeparated : ∀ (x y : R) → (∀ (z : R₊) → abs(x - y) < ⟨ z ⟩₊) → x ≡ y
    selfSeparated x y ∀[•]∣x-y∣<• =
      let
        ∣x-y∣≤0 : abs(x - y) ≤ 0r
        ∣x-y∣≤0 = ¬<→≥ 0r (abs(x - y)) λ 0<∣x-y∣ → is-irrefl (abs(x - y)) $ begin<
          abs(x - y) <⟨ ∀[•]∣x-y∣<• (abs(x - y) , 0<∣x-y∣) ⟩
          abs(x - y) ◾

        x-y≡0 : x - y ≡ 0r
        x-y≡0 = abs≤0→≡0 (x - y) ∣x-y∣≤0
      in
        equalByDifference x y x-y≡0

    _⊔₊_ : R₊ → R₊ → R₊
    (x ⊔₊ y) .fst = ⟨ x ⟩₊ ⊔ ⟨ y ⟩₊
    (x ⊔₊ y) .snd = begin< 0r <⟨ snd x ⟩ ⟨ x ⟩₊ ≤⟨ L≤⊔ ⟩ ⟨ x ⟩₊ ⊔ ⟨ y ⟩₊ ◾

    plusMinus₊ : ∀ x y → (x +₊ y) -₊ y ≡ ⟨ x ⟩₊
    plusMinus₊ (x , _) (y , _) = solve! RCR

    minusPlus₊ : ∀ x y → x -₊ y + ⟨ y ⟩₊ ≡ ⟨ x ⟩₊
    minusPlus₊ (x , _) (y , _) = solve! RCR

    ≡₊→0< : ∀ {x} y → x ≡ ⟨ y ⟩₊ → 0r < x
    ≡₊→0< y p = subst (0r <_) (sym p) (snd y)

    infixl 6 -₊<
    -₊< : ∀ x y → y <₊ x → R₊
    -₊< x y y<x = (x -₊ y) , (<→0<Δ ⟨ y ⟩₊ ⟨ x ⟩₊ y<x)

    syntax -₊< x y y<x = x -₊[ y<x ] y

    <₊SumLeft : ∀ x y → x <₊ x +₊ y
    <₊SumLeft (x , _) (y , 0<y) = begin<
      x ≡→≤⟨ solve! RCR ⟩ x + 0r <⟨ +MonoL< _ _ _ 0<y ⟩ x + y ◾

    <₊SumRight : ∀ x y → x <₊ y +₊ x
    <₊SumRight (x , _) (y , 0<y) = begin<
      x ≡→≤⟨ solve! RCR ⟩ 0r + x <⟨ +MonoR< _ _ _ 0<y ⟩ y + x ◾

    Δ<₊ : ∀ x y → x -₊ y < ⟨ x ⟩₊
    Δ<₊ (x , _) (y , 0<y) = begin<
      x - y <⟨ +MonoL< _ _ _ (-Flip< 0r y 0<y) ⟩ x - 0r ≡→≤⟨ solve! RCR ⟩ x ◾

  module NonNegative
    (0≤+Closed : (x y : R) → 0r ≤ x → 0r ≤ y → 0r ≤ x + y)
    (0≤·Closed : (x y : R) → 0r ≤ x → 0r ≤ y → 0r ≤ x · y)
    where

    open AdditiveAndMultiplicativeSubType
      (0r ≤_) (is-prop-valued≤ 0r) 0≤+Closed 0≤·Closed public renaming (
        subtype to R₀₊ ; isSetSubtype to isSetR₀₊ ; ι to ⟨_⟩₀₊ ; subtype≡ to R₀₊≡
      ; _+subtype_ to _+₀₊_ ; _·subtype_ to _·₀₊_ ; _-subtype_ to _-₀₊_
      ; _≤subtype_ to _≤₀₊_ ; _<subtype_ to _<₀₊_)

    open OrderedCommRingTheory

    R₀₊CommSemiring : CommSemiring _
    fst R₀₊CommSemiring = R₀₊
    CommSemiringStr.0r  (snd R₀₊CommSemiring) = 0r , is-refl _
    CommSemiringStr.1r  (snd R₀₊CommSemiring) = 1r , <-≤-weaken _ _ 0<1
    CommSemiringStr._+_ (snd R₀₊CommSemiring) = _+₀₊_
    CommSemiringStr._·_ (snd R₀₊CommSemiring) = _·₀₊_
    CommSemiringStr.isCommSemiring (snd R₀₊CommSemiring) =
      makeIsCommSemiring
        isSetR₀₊
        (λ _ _ _ → R₀₊≡ (+Assoc _ _ _))
        (λ _     → R₀₊≡ (+IdR _))
        (λ _ _   → R₀₊≡ (+Comm _ _))
        (λ _ _ _ → R₀₊≡ (·Assoc _ _ _))
        (λ _     → R₀₊≡ (·IdR _))
        (λ _ _ _ → R₀₊≡ (·DistR+ _ _ _))
        (λ _     → R₀₊≡ (0LeftAnnihilates _))
        (λ _ _   → R₀₊≡ (·Comm _ _))

    open CommSemiringStr (snd R₀₊CommSemiring) public hiding (_+_ ; _·_)
      renaming (
        0r to 0₀₊ ; 1r to 1₀₊
      ; +Assoc to +₀₊Assoc ; +IdL to +₀₊IdL ; +IdR to +₀₊IdR ; +Comm to +₀₊Comm
      ; ·Assoc to ·₀₊Assoc ; ·IdL to ·₀₊IdL ; ·IdR to ·₀₊IdR ; ·Comm to ·₀₊Comm
      ; ·DistL+ to ·₀₊DistL+₀₊ ; ·DistR+ to ·₀₊DistR+₀₊
      ; AnnihilL to AnnihilL₀₊ ; AnnihilR to AnnihilR₀₊)

    _⊔₀₊_ : R₀₊ → R₀₊ → R₀₊
    (x ⊔₀₊ y) .fst = ⟨ x ⟩₀₊ ⊔ ⟨ y ⟩₀₊
    (x ⊔₀₊ y) .snd = begin≤ 0r ≤⟨ snd x ⟩ ⟨ x ⟩₀₊ ≤⟨ L≤⊔ ⟩ ⟨ x ⟩₀₊ ⊔ ⟨ y ⟩₀₊ ◾

    _⊓₀₊_ : R₀₊ → R₀₊ → R₀₊
    (x ⊓₀₊ y) .fst = ⟨ x ⟩₀₊ ⊓ ⟨ y ⟩₀₊
    (x ⊓₀₊ y) .snd = ⊓GLB (snd x) (snd y)

    plusMinus₀₊ : ∀ x y → (x +₀₊ y) -₀₊ y ≡ ⟨ x ⟩₀₊
    plusMinus₀₊ (x , _) (y , _) = solve! RCR

    minusPlus₀₊ : ∀ x y → x -₀₊ y + ⟨ y ⟩₀₊ ≡ ⟨ x ⟩₀₊
    minusPlus₀₊ (x , _) (y , _) = solve! RCR

    ≡₀₊→0≤ : ∀ {x} y → x ≡ ⟨ y ⟩₀₊ → 0r ≤ x
    ≡₀₊→0≤ y p = subst (0r ≤_) (sym p) (snd y)

    infixl 6 -₀₊≤
    -₀₊≤ : ∀ x y → y ≤₀₊ x → R₀₊
    -₀₊≤ x y y≤x = (x -₀₊ y) , (≤→0≤Δ ⟨ y ⟩₀₊ ⟨ x ⟩₀₊ y≤x)

    syntax -₀₊≤ x y y≤x = x -₀₊[ y≤x ] y

    ≤₀₊SumLeft : ∀ x y → x ≤₀₊ x +₀₊ y
    ≤₀₊SumLeft (x , _) (y , 0≤y) = begin≤
      x ≡→≤⟨ solve! RCR ⟩ x + 0r ≤⟨ +MonoL≤ _ _ _ 0≤y ⟩ x + y ◾

    ≤₀₊SumRight : ∀ x y → x ≤₀₊ y +₀₊ x
    ≤₀₊SumRight (x , _) (y , 0≤y) = begin≤
      x ≡→≤⟨ solve! RCR ⟩ 0r + x ≤⟨ +MonoR≤ _ _ _ 0≤y ⟩ y + x ◾

    Δ≤₀₊ : ∀ x y → x -₀₊ y ≤ ⟨ x ⟩₀₊
    Δ≤₀₊ (x , _) (y , 0≤y) = begin≤
      x - y ≤⟨ +MonoL≤ _ _ _ (-Flip≤ 0r y 0≤y) ⟩ x - 0r ≡→≤⟨ solve! RCR ⟩ x ◾

  private
    2r = 1r + 1r

  module Characteristic≠2 (1/2 : R) (1/2≡2⁻¹ : 1/2 · 2r ≡ 1r) where
    open OrderedCommRingTheory

    1/2+1/2≡1 : 1/2 + 1/2 ≡ 1r
    1/2+1/2≡1 =
      1/2 + 1/2 ≡⟨ solve! RCR ⟩
      1/2 · 2r  ≡⟨ 1/2≡2⁻¹ ⟩
      1r        ∎

    0<1/2 : 0r < 1/2
    0<1/2 = flip (PT.rec (is-prop-valued< 0r 1/2))
      (posSum→pos∨pos 1/2 1/2 (subst (0r <_) (sym 1/2+1/2≡1) 0<1)) λ
      { (inl 0<1/2) → 0<1/2
      ; (inr 0<1/2) → 0<1/2
      }

    0≤1/2 : 0r ≤ 1/2
    0≤1/2 = <-≤-weaken _ _ 0<1/2

    _/2 : R → R
    _/2 = _· 1/2

    _/4 : R → R
    _/4 = _/2 ∘ _/2

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

    /2+/2≡id : ∀ x → x /2 + x /2 ≡ x
    /2+/2≡id x = solve! RCR ∙ meanIdem x

    id-/2≡/2 : ∀ x → x - x /2 ≡ x /2
    id-/2≡/2 x = cong (_- x /2) (sym (/2+/2≡id x)) ∙ solve! RCR

    /4+/4≡/2 : ∀ x → x /4 + x /4 ≡ x /2
    /4+/4≡/2 = /2+/2≡id ∘ (_/2)

    /4+/4+/4+/4≡id : ∀ x → (x /4 + x /4) + (x /4 + x /4) ≡ x
    /4+/4+/4+/4≡id x = cong (∘diag _+_) (/4+/4≡/2 x) ∙ /2+/2≡id x


    /2-/4≡/4 : ∀ x → x /2 - x /4 ≡ x /4
    /2-/4≡/4 = id-/2≡/2 ∘ (_/2)

    id-[/4+/4]≡/2 : ∀ x → x - (x /4 + x /4) ≡ x /2
    id-[/4+/4]≡/2 x = cong (_-_ x) (/4+/4≡/2 x) ∙ id-/2≡/2 x

  module PositiveHalves
    (1/2 : R)
    (1/2≡2⁻¹ : 1/2 · 2r ≡ 1r)
    (0<+Closed : (x y : R) → 0r < x → 0r < y → 0r < x + y)
    (0<·Closed : (x y : R) → 0r < x → 0r < y → 0r < x · y)
    where

    open Characteristic≠2 1/2 1/2≡2⁻¹
    open Positive 0<+Closed 0<·Closed
    open OrderedCommRingTheory

    _/2₊ : R₊ → R₊
    _/2₊ = _·₊ (1/2 , 0<1/2)

    _/4₊ : R₊ → R₊
    _/4₊ = _/2₊ ∘ _/2₊

    /2₊<id : ∀ x → (x /2₊) <₊ x
    /2₊<id x = begin<
      ⟨ x /2₊ ⟩₊            <⟨ <₊SumLeft (x /2₊) (x /2₊) ⟩
      ⟨ x /2₊ +₊ x /2₊ ⟩₊ ≡→≤⟨ /2+/2≡id ⟨ x ⟩₊ ⟩
      ⟨ x ⟩₊                ◾

    /4₊</2₊ : ∀ x → (x /4₊) <₊ (x /2₊)
    /4₊</2₊ = /2₊<id ∘ _/2₊

    /4₊<id : ∀ x → (x /4₊) <₊ x
    /4₊<id x = begin<
      ⟨ x /4₊ ⟩₊ <⟨ /4₊</2₊ x ⟩
      ⟨ x /2₊ ⟩₊ <⟨ /2₊<id x ⟩
      ⟨ x ⟩₊     ◾

    id-/2₊ : ∀ x → 0r < x -₊ (x /2₊)
    id-/2₊ x = subst (0r <_) (sym (id-/2≡/2 ⟨ x ⟩₊)) (snd (x /2₊))

    id-[/4+/4]₊ : ∀ x → 0r < x -₊ (x /4₊ +₊ x /4₊)
    id-[/4+/4]₊ x = subst (0r <_) (cong (_-_ ⟨ x ⟩₊) (sym (/4+/4≡/2 ⟨ x ⟩₊))) (id-/2₊ x)
