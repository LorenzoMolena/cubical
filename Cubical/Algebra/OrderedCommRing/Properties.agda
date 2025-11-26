module Cubical.Algebra.OrderedCommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP using (TypeWithStr)

open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Base

open import Cubical.Relation.Binary.Order.Poset using ()
open import Cubical.Relation.Binary.Order.Pseudolattice


private
  variable
    ℓ ℓ' ℓ'' : Level

OrderedCommRing→Ring : OrderedCommRing ℓ ℓ' → Ring ℓ
OrderedCommRing→Ring = CommRing→Ring ∘ OrderedCommRing→CommRing
{-
OrderedCommRing→Poset : {!   !}
OrderedCommRing→Poset = {! Pseudolattice→Poset ∘ OrderedCommRing→PseudoLattice  !}

OrderedCommRing→Quoset : {!   !}
OrderedCommRing→Quoset = {!   !}
-}


module _ (R' : OrderedCommRing ℓ ℓ') where
  R = fst R'
  open OrderedCommRingStr (snd R')
  open RingTheory (OrderedCommRing→Ring R')

{-
  module OrderedCommRingTheory where
    -Flip< : ∀ (x y : ℚ) → x <ℚ y → - y <ℚ - x
    -Flip< x y x<y = Q.begin<
    - y           ≡→≤⟨ sym $ +Assoc x (- x) (- y) ∙∙ cong (_- y) (+InvR x) ∙∙ +IdL (- y)  ⟩
    x + (- x - y)   <⟨ +MonoR< x y (- x - y) x<y ⟩
    y + (- x - y) ≡→≤⟨ +Assoc-comm1 y (- x) (- y) ∙∙ cong (- x +_) (+InvR y) ∙∙ +IdR (- x) ⟩
    - x          ◾

    +MonoL< : ∀ (x y z : ℚ) → x <ℚ y → z + x <ℚ z + y
    +MonoL< x y z x<y = begin<
      z + x ≡→≤⟨ +Comm z x ⟩ x + z <⟨ +MonoR< x y z x<y ⟩ y + z ≡→≤⟨ +Comm y z ⟩ z + y ◾

    +MonoL≤ : ∀ (x y z : ℚ) → x ≤ℚ y → z + x ≤ℚ z + y
    +MonoL≤ x y z x≤y = begin≤
      z + x ≡→≤⟨ +Comm z x ⟩ x + z ≤⟨ +MonoR≤ x y z x≤y ⟩ y + z ≡→≤⟨ +Comm y z ⟩ z + y ◾

    ·MonoL< : ∀ (x y z : ℚ) → 0 <ℚ z → x <ℚ y → z · x <ℚ z · y
    ·MonoL< x y z 0<z x<y = begin<
      z · x ≡→≤⟨ ·Comm z x ⟩ x · z <⟨ ·MonoR< x y z 0<z x<y ⟩ y · z ≡→≤⟨ ·Comm y z ⟩ z · y ◾

    ·MonoL≤ : ∀ (x y z : ℚ) → 0 ≤ℚ z → x ≤ℚ y → z · x ≤ℚ z · y
    ·MonoL≤ x y z 0≤z x≤y = begin≤
      z · x ≡→≤⟨ ·Comm z x ⟩ x · z ≤⟨ ·MonoR≤ x y z 0≤z x≤y ⟩ y · z ≡→≤⟨ ·Comm y z ⟩ z · y ◾



  module AdditiveSubType
    (P : R → hProp ℓ'')
    (+Closed : (x y : R) → ⟨ P x ⟩ → ⟨ P y ⟩ → ⟨ P (x + y) ⟩)
    where

    subtype = Σ[ x ∈ R ] ⟨ P x ⟩

  module AdditiveAndMultiplicativeSubType
    (P : R → hProp ℓ'')
    (+Closed : (x y : R) → ⟨ P x ⟩ → ⟨ P y ⟩ → ⟨ P (x + y) ⟩)
    (·Closed : (x y : R) → ⟨ P x ⟩ → ⟨ P y ⟩ → ⟨ P (x · y) ⟩)
    where
    open AdditiveSubType P +Closed public


  module Positive where
    private
      0<ₚ_ : R → hProp ℓ'
      0<ₚ x = (0r < x) , is-prop-valued< 0r x
      0<+Closed : ∀ x y → 0r < x → 0r < y → 0r < x + y
      0<+Closed x y 0<x 0<y = subst (_< x + y) (+IdL 0r) {! +MonoL< 0 x y  !}

      0<·Closed : ∀ x y → 0r < x → 0r < y → 0r < x · y
      0<·Closed x y = {!   !}
      open AdditiveAndMultiplicativeSubType 0<ₚ_ 0<+Closed 0<·Closed
        renaming (subtype to R₊)

  module NonNegative where

  module Negative where

  module NonPositive where
-- -}
