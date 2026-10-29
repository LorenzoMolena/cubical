module Cubical.Data.Rationals.Floor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Floor
open import Cubical.Algebra.OrderedCommRing.Instances.Fast.Int
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Nat as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Nat.Mod renaming
  (quotient_/_ to ⌊_/_⌋ ; remainder_/_ to _%_)
open import Cubical.Data.Fast.Int.Base as ℤ using (ℤ ; pos ; negsuc)
open import Cubical.Data.Fast.Int.Properties as ℤ
import Cubical.Data.Fast.Int.Order as ℤ
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Properties
open import Cubical.Data.Rationals.Order
open import Cubical.Data.Sigma

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open FloorCeil ℚOrderedCommRing ℤ↪ℚOCR

floorℚ : ∀ q → Floor q
floorℚ = SQ.ElimProp.go onFrac module Floorℚ where
  open ElimProp
  open Floor
  onFrac : ElimProp λ z → Floor z
  onFrac .fun (pos n    , 1+ d)   .⌊_⌋    = pos ⌊ n / suc d ⌋
  onFrac .fun (pos n    , 1+ d)   .⌊⌋≤    = inj (ℤ.≤ℕ→≤ℤ _ _ $
    subst (⌊ n / suc d ⌋ ℕ.· suc d ℕ.≤_) (sym (·-identityʳ n)) (/·≤ n (suc d)))
  onFrac .fun (pos n , 1+ d)      .<suc⌊⌋ = inj (ℤ.<ℕ→<ℤ _ _ $
    subst (ℕ._< suc ⌊ n / suc d ⌋ ℕ.· suc d) (sym (·-identityʳ n)) (<suc/· n d))
  onFrac .fun (negsuc n , (1+ d)) .⌊_⌋    = negsuc ⌊ n / suc d ⌋
  onFrac .fun (negsuc n , (1+ d)) .⌊⌋≤    = inj (ℤ.-Dist≤ $
    ℤ.<→suc≤ $ _<_.prf $ onFrac .fun (pos n , 1+ d) .<suc⌊⌋)
  onFrac .fun (negsuc n , (1+ d)) .<suc⌊⌋ = inj (ℤ.recompute< $
    subst2 ℤ._<_ (sym (ℤ.·IdR _)) (-DistL· _ _ ∙ sym (congL ℤ._·_ (sucℤ[negsuc]-pos _)))
      (ℤ.-Dist< $ ℤ.≤→<suc $ ℤ.≤ℕ→≤ℤ _ _ (/·≤ n (suc d))))
  onFrac .prop = isPropFloor

ceilℚ : ∀ q → Ceil q
ceilℚ q = -Floor→Ceil q (floorℚ (- q))

open FloorProperties floorℚ public
open CeilProperties  ceilℚ  public

private
  _ : ⌊ [ 4096 / 1000 ] ⌋ ≡ 4
  _ = refl

  _ : ⌈ [ 4096 / 1000 ] ⌉ ≡ 5
  _ = refl

  _ : ⌊ [ -4096 / 1000 ] ⌋ ≡ -5
  _ = refl

  _ : ⌈ [ -4096 / 1000 ] ⌉ ≡ -4
  _ = refl
