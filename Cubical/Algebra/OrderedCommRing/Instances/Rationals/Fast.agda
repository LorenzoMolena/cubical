module Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Data.Nat as ℕ hiding (_+_ ; _·_)
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Int.Fast as ℤ hiding (_+_ ; _-_ ; -_ ; _·_)
import Cubical.Data.Int.Fast.Order as ℤ

open import Cubical.Data.Rationals.Fast as ℚ
  renaming (_+_ to _+ℚ_ ; _-_ to _-ℚ_; -_ to -ℚ_ ; _·_ to _·ℚ_)
open import Cubical.Data.Rationals.Fast.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals.Fast

open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Properties

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Rationals.Fast

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Rationals.Fast

open CommRingStr
open OrderedCommRingStr
open PseudolatticeStr
open StrictOrderStr

ℚOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
fst ℚOrderedCommRing = ℚ
0r  (snd ℚOrderedCommRing) = 0
1r  (snd ℚOrderedCommRing) = 1
_+_ (snd ℚOrderedCommRing) = _+ℚ_
_·_ (snd ℚOrderedCommRing) = _·ℚ_
-_  (snd ℚOrderedCommRing) = -ℚ_
_<_ (snd ℚOrderedCommRing) = _<ℚ_
_≤_ (snd ℚOrderedCommRing) = _≤ℚ_
isOrderedCommRing (snd ℚOrderedCommRing) = isOrderedCommRingℚ
  where
  open IsOrderedCommRing

  isOrderedCommRingℚ : IsOrderedCommRing 0 1 _+ℚ_ _·ℚ_ -ℚ_ _<ℚ_ _≤ℚ_
  isOrderedCommRingℚ .isCommRing      = ℚCommRing .snd .isCommRing
  isOrderedCommRingℚ .isPseudolattice = ℚ≤Pseudolattice .snd .is-pseudolattice
  isOrderedCommRingℚ .isStrictOrder   = ℚ<StrictOrder .snd .isStrictOrder
  isOrderedCommRingℚ .<-≤-weaken      = <Weaken≤
  isOrderedCommRingℚ .≤≃¬>            = λ x y →
    propBiimpl→Equiv (isProp≤ x y) (isProp¬ (y <ℚ x)) (≤→≯  x y) (≮→≥ y x)
  isOrderedCommRingℚ .+MonoR≤         = ≤-+o
  isOrderedCommRingℚ .+MonoR<         = <-+o
  isOrderedCommRingℚ .posSum→pos∨pos  = λ x y → ∣_∣₁ ∘ 0<+ x y
  isOrderedCommRingℚ .<-≤-trans       = isTrans<≤
  isOrderedCommRingℚ .≤-<-trans       = isTrans≤<
  isOrderedCommRingℚ .·MonoR≤         = ≤-·o
  isOrderedCommRingℚ .·MonoR<         = <-·o
  isOrderedCommRingℚ .0<1             = pos<pos tt

module 1/2∈ℚ = Characteristic≠2 ℚOrderedCommRing [ 1 / 2 ] (eq/ _ _ refl)

module PositiveRationals where
  private
    ℚCR  = OrderedCommRing→CommRing ℚOrderedCommRing

    opaque
      0<+Closed : ∀ x y → 0 <ℚ x → 0 <ℚ y → 0 <ℚ x +ℚ y
      0<+Closed = SQ.elimProp2 (λ _ _ → isProp→ (isProp→ (isProp< 0 _))) λ
        { (pos (suc n) , _) (pos (suc m) , _) (pos<pos p) (pos<pos q) → pos<pos tt }

      0<·Closed : ∀ x y → 0 <ℚ x → 0 <ℚ y → 0 <ℚ x ·ℚ y
      0<·Closed = SQ.elimProp2 (λ _ _ → isProp→ (isProp→ (isProp< 0 _))) λ
        { (pos (suc n) , _) (pos (suc m) , _) (pos<pos p) (pos<pos q) → pos<pos tt   }

  open Units ℚCommRing
  open CommRingTheory ℚCommRing
  open OrderedCommRingReasoning ℚOrderedCommRing

  open Positive ℚOrderedCommRing 0<+Closed 0<·Closed public renaming (
      R₊ to ℚ₊ ; isSetR₊ to isSetℚ₊ ; R₊≡ to ℚ₊≡
    ; R₊AdditiveSemigroup to +ℚ₊Semigroup ; R₊MultiplicativeCommMonoid to ·ℚ₊CommMonoid)
  open module PositiveHalvesℚ =
    PositiveHalves ℚOrderedCommRing [ 1 / 2 ] (eq/ _ _ refl) 0<+Closed 0<·Closed

  -- Natural number literals for ℚ

  open import Cubical.Data.Nat.Literals public

  instance
    fromNatℚ₊ : HasFromNat ℚ₊
    fromNatℚ₊ = record { Constraint = λ { zero → ⊥ ; _ → Unit }
                       ; fromNat = λ { (suc n) .fst → [ pos (suc n) / 1 ]
                                     ; (suc n) .snd → pos<pos tt } }

  [_/_]₊ : ℕ₊₁ → ℕ₊₁ → ℚ₊
  [ 1+ n / 1+ m ]₊ = [ pos (suc n) / 1+ m ] , pos<pos tt

  max₊ : ℚ₊ → ℚ₊ → ℚ₊
  fst (max₊ x y) = ℚ.max (fst x) (fst y)
  snd (max₊ x y) = makeOpaque $ elimProp2
    {P = λ a b → 0 <ℚ a → 0 <ℚ b → 0 <ℚ ℚ.max a b}
    (λ a b → isPropΠ2 λ _ _ → isProp< 0 (ℚ.max a b))
    (λ { (pos (suc n) , 1+ a) (pos (suc m) , 1+ b) (pos<pos p) (pos<pos q) →
    let
      1+n = suc n ; 1+m = suc m ; 1+a = suc a ; 1+b = suc b
    in
      -- NOTE :
      -- if we are only concerned about efficiency, then there is no need to recompute,
      -- as `maxSuc` already reduces efficiently to refl for concrete (large) numbers
      -- however, since `_<_` is an indexed data type, we recompute anyway to avoid
      -- `transpX-_<_` in the normal form
      inj (ℤ.recompute< (subst (0 ℤ.<_)
      (sym $ cong (pos ∘ (ℕ._· 1)) $ maxSuc {predℕ (1+n ℕ.· 1+b)} {predℕ (1+m ℕ.· 1+a)})
      (ℤ.pos<pos tt))) })
    (fst x) (fst y) (snd x) (snd y)

  min₊ : ℚ₊ → ℚ₊ → ℚ₊
  fst (min₊ x y) = ℚ.min (fst x) (fst y)
  snd (min₊ x y) = makeOpaque $ elimProp2
    {P = λ a b → 0 <ℚ a → 0 <ℚ b → 0 <ℚ ℚ.min a b}
    (λ a b → isPropΠ2 λ _ _ → isProp< 0 (ℚ.min a b))
    (λ { (pos (suc n) , 1+ a) (pos (suc m) , 1+ b) (pos<pos p) (pos<pos q) →
    let
      1+n = suc n ; 1+m = suc m ; 1+a = suc a ; 1+b = suc b
    in
      inj (ℤ.recompute< (subst (0 ℤ.<_)
      (sym $ cong (pos ∘ (ℕ._· 1)) $ minSuc {predℕ (1+n ℕ.· 1+b)} {predℕ (1+m ℕ.· 1+a)})
      (ℤ.pos<pos tt))) })
    (fst x) (fst y) (snd x) (snd y)

  min₊≤L : ∀ ε δ → min₊ ε δ ≤₊ ε
  min₊≤L ε δ = min≤ ⟨ ε ⟩₊ ⟨ δ ⟩₊

  min₊≤R : ∀ ε δ → min₊ ε δ ≤₊ δ
  min₊≤R ε δ = ℚ.recompute≤ $
    subst (_≤ℚ ⟨ δ ⟩₊) (ℚ.minComm ⟨ δ ⟩₊ ⟨ ε ⟩₊) (min≤ ⟨ δ ⟩₊ ⟨ ε ⟩₊)

  min/2₊<L : ∀ ε δ → (min₊ ε δ /2₊) <₊ ε
  min/2₊<L ε δ = begin<
    ⟨ min₊ ε δ /2₊ ⟩₊ <⟨ /2₊<id (min₊ ε δ) ⟩
    ⟨ min₊ ε δ ⟩₊     ≤⟨ min₊≤L ε δ ⟩
    ⟨ ε ⟩₊            ◾

  min/2₊<R : ∀ ε δ → (min₊ ε δ /2₊) <₊ δ
  min/2₊<R ε δ = begin<
    ⟨ min₊ ε δ /2₊ ⟩₊ <⟨ /2₊<id (min₊ ε δ) ⟩
    ⟨ min₊ ε δ ⟩₊     ≤⟨ min₊≤R ε δ ⟩
    ⟨ δ ⟩₊            ◾

  module ℚ₊Inverse where

    Σinverseℚ₊ : ((ε , 0<ε) : ℚ₊) → Σ[ δ ∈ ℚ ] (ε ℚ.· δ ≡ 1)
    Σinverseℚ₊ = uncurry $ SQ.elimProp (λ ε → isPropΠ λ _ → inverseUniqueness ε) λ
      { (pos (suc n) , 1+ d) (pos<pos p) .fst → [ pos (suc d) , 1+ n ]
      ; (pos (suc n) , 1+ d) (pos<pos p) .snd →
      let
        1+n = pos (suc n) ; 1+d = pos (suc d) ; 1+n·1+d = 1+ d ·₊₁ 1+ n
      in
        [ 1+n ℤ.· 1+d / 1+n·1+d ]  ≡⟨ cong [_/ 1+n·1+d ] (ℤ.·Comm 1+n 1+d) ⟩
        [ 1+d ℤ.· 1+n / 1+n·1+d ]  ≡⟨ ℚ.·CancelR (1+ n) ⟩
        [ 1+d / 1+ d ]             ≡⟨ sym $ cong₂ [_/_] (ℤ.·IdL _) (·₊₁-identityˡ (1+ d))⟩
        [ 1 ℤ.· 1+d / 1 ·₊₁ 1+ d ] ≡⟨ ℚ.·CancelR (1+ d) ⟩
        [ 1 / 1 ]                  ∎ }

    infixl 7 _⁻¹₊

    _⁻¹₊ : ℚ₊ → ℚ₊
    fst (ε ⁻¹₊) = fst (Σinverseℚ₊ ε)
    snd (ε ⁻¹₊) = uncurry (
      SQ.elimProp (λ ε → isPropΠ λ p → isProp< 0 (fst (Σinverseℚ₊ (ε , p)))) (λ
      { (pos (suc n) , 1+ d) (pos<pos p) → pos<pos tt }))
      ε

    _/_ : ℚ₊ → ℚ₊ → ℚ₊
    ε / L = ε ·₊ (L ⁻¹₊)

    ⁻¹inverse : ∀ ε → ⟨ ε / ε ⟩₊ ≡ 1
    ⁻¹inverse = snd ∘ Σinverseℚ₊

    ·/ : ∀ L ε → ⟨ L ·₊ (ε / L) ⟩₊ ≡ ⟨ ε ⟩₊
    ·/ L ε =
      ⟨ L ·₊ (ε ·₊ (L ⁻¹₊)) ⟩₊ ≡⟨ ·CommAssocl ⟨ L ⟩₊ ⟨ ε ⟩₊ ⟨ L ⁻¹₊ ⟩₊ ⟩
      ⟨ ε ·₊ (L ·₊ (L ⁻¹₊)) ⟩₊ ≡⟨ cong (⟨ ε ⟩₊ ℚ.·_) (⁻¹inverse L) ⟩
      ⟨ ε ⟩₊ ℚ.· 1             ≡⟨ ℚ.·IdR ⟨ ε ⟩₊ ⟩
      ⟨ ε ⟩₊                   ∎
