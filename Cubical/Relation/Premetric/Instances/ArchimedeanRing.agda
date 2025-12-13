module Cubical.Relation.Premetric.Instances.ArchimedeanRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence


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

open import Cubical.Algebra.Ring

open import Cubical.Algebra.ArchimedeanRing.Base
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open import Cubical.Relation.Nullary

open import Cubical.Relation.Premetric.Base
open PremetricStr

private variable
  ℓ ℓ' : Level

module _ (R' : ArchimedeanRing ℓ ℓ') where
  private
    R    = fst R'
    ROCR = ArchimedeanRing→OrderedCommRing R'
    RCR  = OrderedCommRing→CommRing ROCR

  open ArchimedeanRingStr (snd R')
  open OrderedCommRingTheory ROCR hiding (·CancelL<)

  open OrderedCommRingReasoning ROCR

{-
  -- w : R → R → (z : ℚ) → (0 ℚ.< z) → hProp ℓ'
  -- w x y [ pos zero    , 1+ b ] = ⊥.rec ∘ ℤ.isIrrefl<
  -- w x y [ pos (suc a) , 1+ b ] = λ _ → (ι₊₁ b · abs(x - y) < ι₊₁ a) , is-prop-valued< _ _
  -- w x y [ negsuc a    , 1+ b ] = ⊥.rec ∘ ℤ.¬pos≤negsuc
  -- w x y (eq/ (pos zero    , (1+ b)) (c , (1+ d)) r i) = {! ⊥.rec ∘ ℤ.isIrrefl<  !}
  -- w x y (eq/ (pos (suc n) , (1+ b)) (c , (1+ d)) r i) = {!   !}
  -- w x y (eq/ (negsuc n    , (1+ b)) (c , (1+ d)) r i) = {!   !}
  -- w x y (squash/ z w p q i j) = (isSetΠ (λ _ → isSetHProp)) _ _ {! p  !} {!  q !} i j

  -- close : R → R → (z : ℚ) → (0 <ℚ z) → hProp ℓ'
  -- close x y = SQ.elim (λ _ → isSetΠ λ _ → isSetHProp)
  --   (λ { (pos zero    , 1+ b) → ⊥.rec ∘ ℤ.isIrrefl<
  --      ; (pos (suc a) , 1+ b) → λ _ → (ι₊₁ b · abs(x - y) < ι₊₁ a) , is-prop-valued< _ _
  --      ; (negsuc n    , 1+ b) → ⊥.rec ∘ ℤ.¬pos≤negsuc })
  --   λ { (pos zero    , 1+ b) (c , 1+ d) p → {!   !}
  --     ; (pos (suc n) , 1+ b) (c , 1+ d) p → {!   !}
  --     ; (negsuc n    , 1+ b) (c , 1+ d) p → {!   !} }



  _≈[_]ₚR_ : R → ℚ₊ → R → hProp ℓ'
  _≈[_]ₚR_ x = flip λ y → uncurry $ SQ.elim {A = ℤ × ℕ₊₁} (λ _ → isSetΠ λ _ → isSetHProp)
    (λ (n , 1+ b) p → (ι₊₁ b · abs(x - y) < ι₀₊ ∣ n ∣ℤ) , is-prop-valued< _ _)
    (λ (n , 1+ b) (m , 1+ d) p → {!   !})

    -- SQ.rec isSetHProp
    -- (λ { (pos zero    , (1+ b)) → ⊥.rec (ℚ.isIrrefl< 0 {!   !})
    --    ; (pos (suc a) , (1+ b)) → {!   !}
    --    ; (negsuc a    , 1+ b)   → {!   !}
    --    })
    -- {!   !} ε

  0<ℤ : ℤ → Type
  0<ℤ (pos zero)    = ⊥
  0<ℤ (pos (suc n)) = Unit
  0<ℤ (negsuc n)    = ⊥

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

  is-prop-valued0<ℚ : ∀ x → isProp (0<ℚ x)
  is-prop-valued0<ℚ = snd ∘ 0<ₚℚ

  0<ℤ→<ℤ : ∀ n → 0<ℤ n → 0 <ℤ n
  0<ℤ→<ℤ (pos (suc n)) 0<ᵗn = ℤ.zero-<possuc

  <ℤ→0<ℤ : ∀ n → 0 <ℤ n → 0<ℤ n
  <ℤ→0<ℤ (pos zero)    = ℤ.isIrrefl<
  <ℤ→0<ℤ (pos (suc n)) = λ _ → tt
  <ℤ→0<ℤ (negsuc n)    = ℤ.¬pos≤negsuc

  0<ℚ→<ℚ : ∀ x → 0<ℚ x → 0 <ℚ x
  0<ℚ→<ℚ = SQ.elimProp (λ x → isProp→ (ℚ.isProp< 0 x))
    λ { (pos (suc n) , (1+ b)) p → n , sym (ℤ.·IdR (pos (suc n))) }

  <ℚ→0<ℚ : ∀ x → 0 <ℚ x → 0<ℚ x
  <ℚ→0<ℚ = SQ.elimProp (λ x → isProp→ (is-prop-valued0<ℚ x))
    λ { (pos zero , (1+ b))    → ℤ.isIrrefl<
      ; (pos (suc n) , (1+ b)) → λ _ → tt
      ; (negsuc n , (1+ b))    → ℤ.¬pos≤negsuc }

  <ℚ≃0<ℚ : ∀ x → (0 <ℚ x) ≃ (0<ℚ x)
  <ℚ≃0<ℚ x = propBiimpl→Equiv (ℚ.isProp< 0 x) (is-prop-valued0<ℚ x) (<ℚ→0<ℚ x) (0<ℚ→<ℚ x)

  <ℚ≡0<ℚ : ∀ x → (0 <ℚ x) ≡ (0<ℚ x)
  <ℚ≡0<ℚ x = ua (<ℚ≃0<ℚ x)

  -- ℚ₊Cases : ∀ {ℓ} → {Y : ℚ₊ → Type ℓ}
  --           → ((x : ℚ) → (p : 0<ℚ x) → Y (x , transport p (sym <ℚ≡0<ℚ)))
  --           → (x : ℚ₊) → (Y x)
  -- ℚ₊Cases {Y = Y} f =
  --   transport (λ X → ((x : X) → (Y x))) (λ i → Σ ℚ λ x → <ℚ≡0<ℚ x (~ i)) $ uncurry f

  _≈[_]ₚ_ : R → ℚ₊ → R → hProp ℓ'
  _≈[_]ₚ_ x = flip λ y →
    subst (λ X → (X → hProp ℓ')) (λ i → Σ ℚ λ x → <ℚ≡0<ℚ x (~ i)) $ uncurry $
    SQ.elim (λ _ → isSetΠ λ _ → isSetHProp)
    (λ { (pos (suc a) , 1+ b) t → (ι₊₁ b · abs(x - y) < ι₊₁ a) , is-prop-valued< _ _ })
    λ { (pos zero    , 1+ b) (pos zero    , 1+ d) p → {! refl   !}
      ; (pos zero    , 1+ b) (pos (suc n) , 1+ d) p → {! ℕ.znots (ℤ.injPos p)  !}
      ; (pos zero    , 1+ b) (negsuc n    , 1+ d) p → {!   !}
      ; (pos (suc n) , 1+ b) (c , 1+ d) p → {!   !}
      ; (negsuc n    , 1+ b) (c , 1+ d) p → {!   !} }

  ≈ᵗ : R → R → (ε : ℚ) → (t : 0<ℚ ε) → hProp ℓ'
  ≈ᵗ x y = SQ.elim (λ _ → isSetΠ λ _ → isSetHProp)
    (λ { (pos (suc a) , 1+ b) t → (ι₊₁ b · abs(x - y) < ι₊₁ a) , is-prop-valued< _ _ })
    λ { (pos zero    , 1+ b) (pos zero    , 1+ d) p → λ i t → {!  !}
      ; (pos zero    , 1+ b) (pos (suc n) , 1+ d) p → ⊥.rec (ℕ.znots (ℤ.injPos p))
      ; (pos zero    , 1+ b) (negsuc n    , 1+ d) p → ⊥.rec (ℤ.posNotnegsuc _ _ p)
      ; (pos (suc m) , 1+ b) (pos zero    , 1+ d) p → ⊥.rec (ℕ.snotz (ℤ.injPos p))
      ; (pos (suc m) , 1+ b) (pos (suc n) , 1+ d) p → {!   !}
      ; (pos (suc m) , 1+ b) (negsuc n    , 1+ d) p → ⊥.rec (ℤ.posNotnegsuc _ _ p)
      ; (negsuc m    , 1+ b) (pos n       , 1+ d) p → ⊥.rec (ℤ.negsucNotpos _ _ p)
      ; (negsuc m    , 1+ b) (negsuc n    , 1+ d) p → {!   !} }

  ≈ᵗ' : R → R → ℚ → hProp ℓ'
  ≈ᵗ' x y = SQ.elim (λ _ → isSetHProp) (uncurry onFractions) respect∼
    module Closeness where
      onFractions : ℤ → ℕ₊₁ → hProp ℓ'
      onFractions (pos zero)    (1+ b) .fst = ⊥*
      onFractions (pos zero)    (1+ b) .snd = isProp⊥*
      onFractions (pos (suc a)) (1+ b) .fst = ι₊₁ b · abs(x - y) < ι₊₁ a
      onFractions (pos (suc a)) (1+ b) .snd = is-prop-valued< _ _
      onFractions (negsuc a)    (1+ b) .fst = ⊥*
      onFractions (negsuc a)    (1+ b) .snd = isProp⊥*

      respect∼ : ((a , b) (c , d) : ℤ × ℕ₊₁)
                 → (r : (a , b) ∼ (c , d))
                 → onFractions a b ≡ onFractions c d
      respect∼ (pos zero    , 1+ b) (pos zero    , 1+ d) = λ _ → refl
      respect∼ (pos zero    , 1+ b) (negsuc c    , 1+ d) = λ _ → refl
      respect∼ (pos zero    , 1+ b) (pos (suc c) , 1+ d) = ⊥.rec ∘ ℕ.znots ∘ ℤ.injPos
      respect∼ (negsuc a    , 1+ b) (pos zero    , 1+ d) = λ _ → refl
      respect∼ (negsuc a    , 1+ b) (negsuc c    , 1+ d) = λ _ → refl
      respect∼ (negsuc a    , 1+ b) (pos (suc c) , 1+ d) = ⊥.rec ∘ ℤ.negsucNotpos _ _
      respect∼ (pos (suc a) , 1+ b) (pos zero    , 1+ d) = ⊥.rec ∘ ℕ.snotz ∘ ℤ.injPos
      respect∼ (pos (suc a) , 1+ b) (negsuc c    , 1+ d) = ⊥.rec ∘ ℤ.posNotnegsuc _ _
      respect∼ (pos (suc a) , 1+ b) (pos (suc c) , 1+ d) = λ p →
        Σ≡Prop (λ _ → isPropIsProp) $
        let
          1+a = pos (suc a) ; 1+b = pos (suc b) ; 1+c = pos (suc c) ; 1+d = pos (suc d)
          ιa = ι₊₁ a ; ιb = ι₊₁ b ; ιc = ι₊₁ c ; ιd = ι₊₁ d
          0<ιa : 0r < ιa
          0<ιa = subst (_< ιa) pres0 (pres< 0 (pos (suc a)) ℤ.zero-<possuc)
          0<ιb : 0r < ιb
          0<ιb = subst (_< ιb) pres0 (pres< 0 (pos (suc b)) ℤ.zero-<possuc)
          0<ιc : 0r < ιc
          0<ιc = subst (_< ιc) pres0 (pres< 0 (pos (suc c)) ℤ.zero-<possuc)
          0<ιd : 0r < ιd
          0<ιd = subst (_< ιd) pres0 (pres< 0 (pos (suc d)) ℤ.zero-<possuc)
        in
          hPropExt (is-prop-valued< _ _) (is-prop-valued< _ _)
          (λ b∣x-y∣<a →
            ·CancelL< _ _ _ 0<ιb $ subst2 _<_ (
              ιd · (ιb · abs(x - y)) ≡⟨ solve! RCR ⟩
              ιb · (ιd · abs(x - y)) ∎)
            (
              ιd · ιa        ≡⟨ solve! RCR ⟩
              ιa · ιd        ≡⟨ sym $ pres· 1+a 1+d ⟩
              ι (1+a ·ℤ 1+d) ≡⟨ cong ι p ⟩
              ι (1+c ·ℤ 1+b) ≡⟨ pres· 1+c 1+b ⟩
              ιc · ιb        ≡⟨ solve! RCR ⟩
              ιb · ιc        ∎)
            (·MonoL< _ _ ιd 0<ιd b∣x-y∣<a))
          λ d∣x-y∣<c →
            ·CancelL< _ _ _ 0<ιd $ subst2 _<_ (
              ιb · (ιd · abs (x - y)) ≡⟨ solve! RCR ⟩
              ιd · (ιb · abs (x - y)) ∎)
            (
              ιb · ιc        ≡⟨ solve! RCR ⟩
              ιc · ιb        ≡⟨ sym $ pres· 1+c 1+b ⟩
              ι (1+c ·ℤ 1+b) ≡⟨ sym $ cong ι p ⟩
              ι (1+a ·ℤ 1+d) ≡⟨ pres· 1+a 1+d ⟩
              ιa · ιd        ≡⟨ solve! RCR ⟩
              ιd · ιa        ∎)
            (·MonoL< _ _ ιb 0<ιb d∣x-y∣<c)

  _≈ᵗ[_]ₚ_ : R → ℚ₊ → R → hProp ℓ'
  _≈ᵗ[_]ₚ_ x ε y = ≈ᵗ' x y (fst ε)


  ArchimedeanRing→PremetricSpace : PremetricSpace ℓ ℓ'
  fst ArchimedeanRing→PremetricSpace = R
  _≈[_]_ (snd ArchimedeanRing→PremetricSpace) x ε y = fst (x ≈ᵗ[ ε ]ₚ y)
  isPremetric (snd ArchimedeanRing→PremetricSpace) = isPM
    where
      open IsPremetric

      isPM : IsPremetric _
      isPM .isSetM = is-set
      isPM .isProp≈ = λ x y ε → snd (x ≈ᵗ[ ε ]ₚ y)
      isPM .isRefl≈ = λ x (ε , 0<ε) → SQ.elimProp (snd ∘ (≈ᵗ' x x))
        (λ { (pos zero    , 1+ b) → {!   !}
           ; (pos (suc n) , 1+ b) → {!   !}
           ; (negsuc n    , 1+ b) → {!   !} }) ε
        -- λ x → uncurry $ SQ.elimProp
        -- (λ ε → isPropΠ λ 0<ε → snd (x ≈[ ε , 0<ε ]ₚ x))
        -- λ { (pos (suc n) , 1+ b) p → begin<
        --   ι₊₁ b · abs(x - x) ≡→≤⟨ _ ≡⟨ cong (ι₊₁ b ·_) (cong abs (solve! RCR) ∙ abs0) ⟩
        --   ι₊₁ b · 0r           ≡⟨ solve! RCR ⟩ (sym pres0) ⟩
        --   ι₀₊ 0                  <⟨ pres< 0 (pos (suc n)) {!   !} ⟩
        --   {!   !} }
      isPM .isSym≈ = {!   !}
      isPM .isSeparated≈ = {!   !}
      isPM .isTriangular≈ = {!   !}
      isPM .isRounded≈ = {!   !}
-- -}
