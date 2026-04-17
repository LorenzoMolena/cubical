module Cubical.Relation.Premetric.Instances.ArchimedeanRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence


open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

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

open import Cubical.Algebra.ArchimedeanRing.Base
open import Cubical.Algebra.ArchimedeanRing.Properties
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast
open import Cubical.Algebra.Ring

open import Cubical.Relation.Nullary
open import Cubical.Relation.Premetric.Base

open PremetricStr

open PositiveRationals hiding (is-set)

private variable
  ℓ ℓ' : Level

module _ (R' : ArchimedeanRing ℓ ℓ') where
  private
    R    = fst R'
    ROCR = ArchimedeanRing→OrderedCommRing R'
    RCR  = ArchimedeanRing→CommRing R'
    RR   = ArchimedeanRing→Ring R'

  open RingTheory RR
  open OrderedCommRingReasoning ROCR
  open ArchimedeanRingStr (snd R')
  open ArchimedeanRingTheory R'

  private
    <₀₊ℚ' : (x : R) → (0r ≤ x) → ℚ → hProp ℓ'
    <₀₊ℚ' x 0≤x = SQ.elim (λ _ → isSetHProp) onFrac onFrac∼
      where
        onFrac : ℤ × ℕ₊₁ → hProp ℓ'
        fst (onFrac (a , 1+ b)) = ι₊₁ b · x < ι a
        snd (onFrac (a , 1+ b)) = is-prop-valued< _ _

        lemma∼ : ∀ a/b c/d → a/b ∼ c/d → fst (onFrac a/b) → fst (onFrac c/d)
        lemma∼ (a , 1+ b) (c , 1+ d) ad≡cb x<a/b =
          ·CancelL< (ι₊₁ d · x) (ι c) (ι a) 0<ιa adx<ac
          where
            1+b = pos (suc b) ; 1+d = pos (suc d)

            0<ιa : 0r < ι a
            0<ιa = begin<
              0r        ≡→≤⟨ sym $ 0LeftAnnihilates x ⟩
              0r · x      ≤⟨ 0≤ι₀₊ (suc b) ≤·[ x , 0≤x ] ⟩
              ι₊₁ b · x   <⟨ x<a/b ⟩
              ι a         ◾

            0<a : 0 <ℤ a
            0<a = reflect< 0 a (subst (_< ι a) (sym pres0) 0<ιa)

            0<c : 0 <ℤ c
            0<c = ℤ.0<o→<-·o-cancel (ℤ.pos<pos tt)
                $ subst (0 <ℤ_) ad≡cb
                $ ℤ.0<o→<-·o (ℤ.pos<pos tt) 0<a

            0<ιc : 0r < ι c
            0<ιc = subst (_< ι c) pres0 (pres< 0 c 0<c)

            adx<ac : ι a · (ι₊₁ d · x) < ι a · ι c
            adx<ac = begin<
              ι a · (ι₊₁ d · x) ≡→≤⟨ _ ≡⟨ ·Assoc _ _ x ⟩
              ι a ·  ι₊₁ d · x    ≡⟨ sym $ cong (_· x) (pres· a 1+d) ⟩
              ι (a ·ℤ 1+d) · x    ≡⟨ cong ((_· x) ∘ ι) ad≡cb ⟩
              ι (c ·ℤ 1+b) · x    ≡⟨ cong (_· x) (pres· c 1+b) ⟩
              ι c ·  ι₊₁ b · x    ≡⟨ sym $ ·Assoc _ _ x ⟩ refl ⟩
              ι c · (ι₊₁ b · x)   <⟨ [ ι c , 0<ιc ]·< x<a/b ⟩
              ι c · ι a         ≡→≤⟨ ·Comm (ι c) (ι a) ⟩
              ι a · ι c           ◾

        onFrac∼ : ∀ a/b c/d → a/b ∼ c/d → onFrac a/b ≡ onFrac c/d
        onFrac∼ a/b c/d r = Σ≡Prop (λ _ → isPropIsProp)
          (hPropExt
            (snd (onFrac a/b)) (snd (onFrac c/d))
            (lemma∼ a/b c/d r) (lemma∼ c/d a/b (sym r)))

    ≈' : R → R → ℚ → hProp ℓ'
    ≈' x y = <₀₊ℚ' (abs(x - y)) (0≤abs(x - y))

  _≈R[_]_ : R → ℚ → R → Type ℓ'
  x ≈R[ ε ] y = fst (≈' x y ε)

  _≈₊R[_]_ : R → ℚ₊ → R → Type ℓ'
  x ≈₊R[ ε ] y = fst (≈' x y ⟨ ε ⟩₊)

  isProp≈R : ∀ x y ε → isProp (x ≈R[ ε ] y)
  isProp≈R x y ε = snd (≈' x y ε)

  isProp≈₊R : ∀ x y ε → isProp (x ≈₊R[ ε ] y)
  isProp≈₊R x y ε = snd (≈' x y ⟨ ε ⟩₊)

  module Close where

    onFracIsRefl≈R : ∀ x a/b 0< → x ≈₊R[ [ a/b ] , 0< ] x
    onFracIsRefl≈R x (pos (suc a) , 1+ b) (ℚ.pos<pos _) =
      subst (_< ι₊₁ a)
        (  sym (cong ((ι₊₁ b ·_) ∘ abs) (+InvR x)
        ∙∙ cong (ι₊₁ b ·_) abs0
        ∙∙ 0RightAnnihilates (ι₊₁ b)))
        (0<ι₊₁ a)

    onFracIsSym≈R : ∀ x y a/b 0< → x ≈₊R[ [ a/b ] , 0< ] y → y ≈₊R[ [ a/b ] , 0< ] x
    onFracIsSym≈R x y a/b 0< = subst (_< ι (fst a/b)) (cong (_ ·_) (abs-Comm x y))

    isSeparated≈R : ∀ x y → (∀ ε → x ≈₊R[ ε ] y) → x ≡ y
    isSeparated≈R x y ∀x≈y = equalByDifference x y (abs≤0→≡0 (x - y) ∣x-y∣≤0) where
      ∣x-y∣≤0 : abs(x - y) ≤ 0r
      ∣x-y∣≤0 = ¬<→≥ 0r (abs(x - y)) λ 0<∣x-y∣ → proof (⊥ , isProp⊥) by do
        (n , 1<ι₊₁n∣x-y∣) ← archimedeanProperty _ _ 0<1 0<∣x-y∣
        let
          ι₊₁n∣x-y∣<1 : ι₊₁ n · abs(x - y) < 1r
          ι₊₁n∣x-y∣<1 = subst (ι₊₁ n · abs(x - y) <_) pres1 (∀x≈y [ 1 / 1+ n ]₊)
        return (is-asym _ _ 1<ι₊₁n∣x-y∣ ι₊₁n∣x-y∣<1)

    onFracIsTriangular≈R : ∀ x y z a/b c/d 0< 0<'
                         → x ≈₊R[ [ a/b ] , 0<  ] y
                         → y ≈₊R[ [ c/d ] , 0<' ] z
                         → x ≈₊R[ ([ a/b ] , 0<) +₊ ([ c/d ] , 0<') ] z
    onFracIsTriangular≈R
      x y z (pos (suc a) , 1+ b) (pos (suc c) , 1+ d) (ℚ.pos<pos _) (ℚ.pos<pos _) b∣x-y∣<a d∣y-z∣<c =
      begin<
      ι (1+b ·ℤ 1+d) · abs(x - z)                               ≤⟨ step0 ⟩
      ι (1+b ·ℤ 1+d) · (abs(x - y) + abs(y - z))              ≡→≤⟨ step1 ⟩
      ι₊₁ b · abs(x - y) · ι₊₁ d + ι₊₁ d · abs(y - z) · ι₊₁ b   <⟨ step2 ⟩
      ι₊₁ a · ι₊₁ d + ι₊₁ c · ι₊₁ b                           ≡→≤⟨ step3 ⟩
      ι (1+a ·ℤ 1+d +ℤ 1+c ·ℤ 1+b)                              ◾
      where
        1+a = pos(suc a) ; 1+b = pos(suc b) ; 1+c = pos(suc c) ; 1+d = pos(suc d)
        step0 = ·MonoL≤ _ _ _ (0≤ι₀₊ _) (triangularInequality- x z y)
        step1 =
          _ ≡⟨ congL _·_ (pres· _ _) ⟩
          ι₊₁ b · ι₊₁ d · (abs(x - y) + abs(y - z)) ≡⟨ solve! RCR ⟩ refl
        step2 = +Mono< _ _ _ _ (·MonoR< _ _ _ (0<ι₊₁ d) b∣x-y∣<a)
                               (·MonoR< _ _ _ (0<ι₊₁ b) d∣y-z∣<c)
        step3 = sym $ pres+ _ _ ∙ cong₂ _+_ (pres· _ _) (pres· _ _)

    onFracIsRounded≈R : ∀ x y a/b 0<
                      → x ≈₊R[ [ a/b ] , 0< ] y
                      → ∃[ δ ∈ ℚ₊ ] (⟨ δ ⟩₊ <ℚ [ a/b ]) × (x ≈₊R[ δ ] y)
    onFracIsRounded≈R x y (pos (suc a) , 1+ b) 0<@(ℚ.pos<pos _) b∣x-y∣<a = do
      (k , ι1<k⟨a-b∣x-y∣⟩) ← archimedeanProperty _ _ (0<ι₊₁ 0) (<→0<Δ _ _ b∣x-y∣<a)
      let
        1+a = pos (suc a) ; 1+b = pos (suc b) ; 1+k = pos (suc k)
        bk  = (1+ b) ℕ₊₁.·₊₁ (1+ k)

        step1 = sym $ λ i → pres· 1+a 1+k i + pres- 1 i - pres· 1+b 1+k i · abs(x - y)
        step2 = sym $ congL _-_ (pres+ _ _)

        lemma : ι (1+b ·ℤ 1+k) · abs(x - y) < ι (1+a ·ℤ 1+k -ℤ 1)
        lemma = 0<Δ→< _ _ $ flip (subst (0r <_)) (<→0<Δ _ _ ι1<k⟨a-b∣x-y∣⟩) $
          ι₊₁ k · (ι₊₁ a - ι₊₁ b · abs(x - y)) - ι₊₁ 0          ≡⟨ solve! RCR ⟩
          ι₊₁ a · ι₊₁ k - ι₊₁ 0 - ι₊₁ b · ι₊₁ k · abs(x - y)    ≡⟨ step1 ⟩
          ι (1+a ·ℤ 1+k) + (ι -1) - ι (1+b ·ℤ 1+k) · abs(x - y) ≡⟨ step2 ⟩
          ι (1+a ·ℤ 1+k -ℤ 1) - ι (1+b ·ℤ 1+k) · abs(x - y)     ∎

        0<ak-1 : 0 <ℤ (1+a ·ℤ 1+k -ℤ 1)
        0<ak-1 = reflect< 0 ((1+a ·ℤ 1+k -ℤ 1)) $ begin<
          ι 0                         ≡→≤⟨ pres0 ∙ solve! RCR ⟩
          ι (1+b ·ℤ 1+k) · 0r          ≤⟨ [ ι (1+b ·ℤ 1+k) , 0≤ι₀₊ _ ]·≤ 0≤abs _ ⟩
          ι (1+b ·ℤ 1+k) · abs(x - y)  <⟨ lemma ⟩
          ι (1+a ·ℤ 1+k -ℤ 1)         ◾

        l , 1+l≡ak-1 = ℤ.<→Σℕ 0<ak-1

        δ : ℚ₊
        δ = [ 1+ l / bk ]₊

        δ<ε : δ <₊ ([ pos(suc a) / 1+ b ] , 0<)
        δ<ε = subst2 (_<ℚ_)
              (sym (cong [_/ bk ] 1+l≡ak-1))
              (ℚ.·CancelR {pos(suc a)} {1+ b} (1+ k))
              (ℚ.<ℤ→<ℚ (1+a ℤ.· 1+k ℤ.- 1) (1+a ℤ.· 1+k) bk (ℤ.-possuc< {k = 0}))

        x≈[δ]y : x ≈₊R[ δ ] y
        x≈[δ]y = subst ((ι (1+b ·ℤ 1+k) · abs(x - y) <_) ∘ ι) (sym 1+l≡ak-1) lemma
      return (δ , δ<ε , x≈[δ]y)

  open IsPremetric
  ArchimedeanRing→PremetricSpace : PremetricSpace ℓ ℓ'
  fst ArchimedeanRing→PremetricSpace = R
  _≈[_]_ (snd ArchimedeanRing→PremetricSpace) = _≈₊R[_]_
  isPremetric (snd ArchimedeanRing→PremetricSpace) = isPM
    where abstract

      isPM : IsPremetric _≈₊R[_]_
      isPM .isSetM        = is-set
      isPM .isProp≈       = isProp≈₊R
      isPM .isRefl≈       = λ x → uncurry $
        SQ.elimProp (λ ε → isPropΠ λ _ → isProp≈R x x ε) (Close.onFracIsRefl≈R x)
      isPM .isSym≈        = λ x y → uncurry $
        SQ.elimProp (λ ε → isPropΠ2 λ _ _ → isProp≈R y x ε) (Close.onFracIsSym≈R x y)
      isPM .isSeparated≈  = Close.isSeparated≈R
      isPM .isTriangular≈ = λ x y z → uncurry $
        SQ.elimProp (λ ε₊ → isPropΠ4 λ _ δ _ _ → isProp≈R x z (ε₊ +ℚ ⟨ δ ⟩₊))
        λ a/b 0< → uncurry $
        SQ.elimProp (λ δ₊ → isPropΠ3 λ _ _ _ → isProp≈R x z ([ a/b ] +ℚ δ₊))
        λ c/d 0<' → Close.onFracIsTriangular≈R x y z a/b c/d 0< 0<'
      isPM .isRounded≈    = λ x y → uncurry $
        SQ.elimProp (λ ε → isPropΠ2 λ _ _ → squash₁) (Close.onFracIsRounded≈R x y)
