module Cubical.Relation.Premetric.MorePremetric.Instances.ArchimedeanRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence


open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)
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

open import Cubical.Algebra.Ring

open import Cubical.Algebra.ArchimedeanRing.Base
open import Cubical.Algebra.ArchimedeanRing.Properties
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast
open import Cubical.Algebra.OrderedCommRing.Instances.Int.Fast

open import Cubical.Relation.Nullary

open import Cubical.Relation.Premetric.MorePremetric.Base
open PremetricStr

private variable
  ℓ ℓ' : Level

module _ (R' : ArchimedeanRing ℓ ℓ') where
  private
    R    = fst R'
    ROCR = ArchimedeanRing→OrderedCommRing R'
    RCR  = OrderedCommRing→CommRing ROCR

  open ArchimedeanRingStr (snd R')
  open ArchimedeanRingTheory R' hiding (·CancelL<)
  open RingTheory (ArchimedeanRing→Ring R')

  open OrderedCommRingReasoning ROCR

  module Closeness (x y : R) where

    onFractions : (n : ℤ) → ℕ₊₁ → fst (ℚ₊.0ℤ<ᵗ n) → hProp ℓ'
    onFractions (pos (suc a)) (1+ b) t .fst = ι₊₁ b · abs(x - y) < ι₊₁ a
    onFractions (pos (suc a)) (1+ b) t .snd = is-prop-valued< _ _

    respect∼ : ∀ x y → x ∼ y → ∀ t t' → uncurry onFractions x t ≡ uncurry onFractions y t'
    respect∼ (pos (suc a) , 1+ b) (pos (suc c) , 1+ d) p t t' =
      let
        1+a = pos (suc a) ; 1+b = pos (suc b) ; 1+c = pos (suc c) ; 1+d = pos (suc d)
      in
      Σ≡Prop (λ _ → isPropIsProp) $ hPropExt (is-prop-valued< _ _) (is-prop-valued< _ _)
      (λ b∣x-y∣<a → ·CancelL< _ _ _ (0<ι₊₁ b) $ subst2 _<_
        (
          ι₊₁ d · (ι₊₁ b · abs(x - y)) ≡⟨ solve! RCR ⟩
          ι₊₁ b · (ι₊₁ d · abs(x - y)) ∎)
        (
          ι₊₁ d · ι₊₁ a  ≡⟨ solve! RCR ⟩
          ι₊₁ a · ι₊₁ d  ≡⟨ sym $ pres· 1+a 1+d ⟩
          ι (1+a ·ℤ 1+d) ≡⟨ cong ι p ⟩
          ι (1+c ·ℤ 1+b) ≡⟨ pres· 1+c 1+b ⟩
          ι₊₁ c · ι₊₁ b  ≡⟨ solve! RCR ⟩
          ι₊₁ b · ι₊₁ c  ∎)
        (·MonoL< _ _ (ι₊₁ d) (0<ι₊₁ d) b∣x-y∣<a))
      λ d∣x-y∣<c → ·CancelL< _ _ _ (0<ι₊₁ d) $ subst2 _<_
        (
          ι₊₁ b · (ι₊₁ d · abs (x - y)) ≡⟨ solve! RCR ⟩
          ι₊₁ d · (ι₊₁ b · abs (x - y)) ∎)
        (
          ι₊₁ b · ι₊₁ c        ≡⟨ solve! RCR ⟩
          ι₊₁ c · ι₊₁ b        ≡⟨ sym $ pres· 1+c 1+b ⟩
          ι (1+c ·ℤ 1+b) ≡⟨ sym $ cong ι p ⟩
          ι (1+a ·ℤ 1+d) ≡⟨ pres· 1+a 1+d ⟩
          ι₊₁ a · ι₊₁ d        ≡⟨ solve! RCR ⟩
          ι₊₁ d · ι₊₁ a        ∎)
        (·MonoL< _ _ (ι₊₁ b) (0<ι₊₁ b) d∣x-y∣<c)

    ≈ₚ : ℚ₊ → hProp ℓ'
    ≈ₚ = uncurry $ SQ.elim (λ _ → isSetΠ λ _ → isSetHProp) (uncurry onFractions)
      λ a b r i t →
      respect∼ a b r
        (transp (λ j → ℚ₊.0<ᵗ (eq/ a b r (i ∧ ~ j))) (~ i) t)
        (transp (λ j → ℚ₊.0<ᵗ (eq/ a b r (j ∨ i))) i t)
        i

  _≈[_]R_ : R → ℚ₊ → R → Type ℓ'
  _≈[_]R_ x ε y = fst (Closeness.≈ₚ x y ε)

  isProp≈R : ∀ x y ε → isProp (x ≈[ ε ]R y)
  isProp≈R x y = snd ∘ Closeness.≈ₚ x y

  onFractionsIsRefl≈R : ∀ x a b t → fst (Closeness.onFractions x x a b t)
  onFractionsIsRefl≈R x (pos (suc a)) (1+ b) t = flip (subst (_< ι₊₁ a)) (0<ι₊₁ a) $
    0r                 ≡⟨ solve! RCR ⟩
    ι₊₁ b · 0r         ≡⟨ sym $ cong (ι₊₁ b ·_) abs0 ⟩
    ι₊₁ b · abs 0r     ≡⟨ cong ((ι₊₁ b ·_) ∘ abs) (solve! RCR) ⟩
    ι₊₁ b · abs(x - x) ∎

  onFractionsIsSym≈R : ∀ x y a b t
                       → fst (Closeness.onFractions x y a b t)
                       → fst (Closeness.onFractions y x a b t)
  onFractionsIsSym≈R x y (pos (suc a)) (1+ b) t =
    subst ((_< ι₊₁ a) ∘ (ι₊₁ b ·_)) (abs-Comm x y)

  isSeparated≈R : ∀ x y → (∀ ε → x ≈[ ε ]R y) → x ≡ y
  isSeparated≈R x y ∀•[x≈•y] =
    let
      ∣x-y∣≤0 : abs(x - y) ≤ 0r
      ∣x-y∣≤0 = ¬<→≥ 0r (abs(x - y)) λ 0<∣x-y∣ → flip (PT.elim (λ _ → isProp⊥))
        (archimedeanProperty (ι 1) (abs(x - y)) (0<ι₊₁ 0) 0<∣x-y∣)
        λ (k , 1<ι₊₁k∣x-y∣) → is-asym (ι 1) (ι₊₁ k · abs(x - y))
          1<ι₊₁k∣x-y∣
          (∀•[x≈•y] ([ 1 / 1+ k ] , tt))
    in
      equalByDifference x y (abs≤0→≡0 (x - y) ∣x-y∣≤0)

  onFractionsIsTriangular≈R : ∀ x y z a b t c d s
                              → fst (Closeness.onFractions x y a b t)
                              → fst (Closeness.onFractions y z c d s)
                              → fst (Closeness.onFractions x z (a ℤ.· ℕ₊₁→ℤ d ℤ.+ c ℤ.· ℕ₊₁→ℤ b) (b ℕ₊₁.·₊₁ d)
                                                               (0<ᵗ+Closed [ a / b ] [ c / d ] t s))
  onFractionsIsTriangular≈R x y z (pos(suc a)) (1+ b) t (pos(suc c)) (1+ d) s b∣x-y∣<a d∣y-z∣<c =
    let
      1+a = pos (suc a) ; 1+b = pos (suc b) ; 1+c = pos (suc c) ; 1+d = pos (suc d)
    in
      begin<
      ι (1+b ℤ.· 1+d) · abs(x - z)                              ≤⟨ step0 ⟩
      ι (1+b ℤ.· 1+d) · (abs(x - y) + abs(y - z))             ≡→≤⟨ step1 ⟩
      ι₊₁ b · abs(x - y) · ι₊₁ d + ι₊₁ d · abs(y - z) · ι₊₁ b   <⟨ step2 ⟩
      ι₊₁ a · ι₊₁ d + ι₊₁ c · ι₊₁ b                           ≡→≤⟨ step3 ⟩
      ι (1+a ℤ.· 1+d ℤ.+ 1+c ℤ.· 1+b) ◾
    where
      step0 = ·MonoL≤ _ _ _ (0≤ι₀₊ _) (triangularInequality- x z y)
      step1 =
        _ ≡⟨ congL _·_ (pres· _ _) ⟩
        ι₊₁ b · ι₊₁ d · (abs(x - y) + abs(y - z)) ≡⟨ solve! RCR ⟩ refl
      step2 = +Mono< _ _ _ _ (·MonoR< _ _ _ (0<ι₊₁ d) b∣x-y∣<a)
                             (·MonoR< _ _ _ (0<ι₊₁ b) d∣y-z∣<c)
      step3 = sym $ pres+ _ _ ∙ cong₂ _+_ (pres· _ _) (pres· _ _)

  onFractionsIsRounded≈R : ∀ x y a b t
                           → fst (Closeness.onFractions x y a b t)
                           → ∃[ δ ∈ ℚ₊ ] δ <₊ ([ a / b ] , t) × (x ≈[ δ ]R y)
  onFractionsIsRounded≈R x y (pos (suc a)) (1+ b) t b∣x-y∣<a = PT.map
    (uncurry f) (archimedeanProperty _ _ (0<ι₊₁ 0) (<→0<- _ _ b∣x-y∣<a))
    where
      f : ∀ k → ι 1 < ι₊₁ k · (ι₊₁ a - ι₊₁ b · abs(x - y))
          → Σ[ δ ∈ ℚ₊ ] (δ <₊ ([ pos (suc a) / 1+ b ] , t)) × x ≈[ δ ]R y
      f k 1<k[a-b∣x-y∣] = δ , δ<ε , x≈[δ]y
        where
          1+a 1+b 1+k : ℤ ; bk : ℕ₊₁
          1+a = pos (suc a) ; 1+b = pos (suc b) ; 1+k = pos (suc k)
          bk  = (1+ b) ℕ₊₁.·₊₁ (1+ k)

          lemma : ι (1+b ℤ.· 1+k) · abs(x - y) < ι (1+a ℤ.· 1+k ℤ.- 1)
          lemma = 0<-→< _ _ $ flip (subst (0r <_)) (<→0<- _ _ 1<k[a-b∣x-y∣]) $
            ι₊₁ k · (ι₊₁ a - ι₊₁ b · abs(x - y)) - ι₊₁ 0            ≡⟨ solve! RCR ⟩
            ι₊₁ a · ι₊₁ k - ι₊₁ 0 - ι₊₁ b · ι₊₁ k · abs(x - y)      ≡⟨ step1 ⟩
            ι (1+a ℤ.· 1+k) + (ι -1) - ι (1+b ℤ.· 1+k) · abs(x - y) ≡⟨ step2 ⟩
            ι (1+a ℤ.· 1+k ℤ.- 1) - ι (1+b ℤ.· 1+k) · abs(x - y)    ∎
            where
              step1 = sym $ λ i → pres· 1+a 1+k i + pres- 1 i - pres· 1+b 1+k i · abs(x - y)
              step2 = sym $ congL _-_ (pres+ _ _)

          0<ak-1 : 0 <ℤ (1+a ℤ.· 1+k ℤ.- 1) ℤ.· 1
          0<ak-1 = reflect< 0 ((1+a ℤ.· 1+k ℤ.- 1) ℤ.· 1) $ begin<
            ι 0                          ≡→≤⟨ pres0 ∙ solve! RCR ⟩
            ι (1+b ℤ.· 1+k) · 0r           ≤⟨ ·MonoL≤ _ _ _ (0≤ι₀₊ _) (0≤abs (x - y)) ⟩
            ι (1+b ℤ.· 1+k) · abs(x - y)   <⟨ lemma ⟩
            ι (1+a ℤ.· 1+k ℤ.- 1)        ≡→≤⟨ sym $ cong ι (ℤ.·IdR _) ⟩
            ι ((1+a ·ℤ 1+k -ℤ 1) ·ℤ 1)     ◾

          0<ᵗak-1 : fst (ℚ₊.0ℤ<ᵗ (1+a ℤ.· 1+k ℤ.- 1))
          0<ᵗak-1 = ℚ₊.<→0<ᵗ [ 1+a ℤ.· 1+k ℤ.- 1 , (1+ b) ℕ₊₁.·₊₁ (1+ k) ] 0<ak-1

          lemma' : Σ[ k ∈ ℕ ] 1+a ℤ.· 1+k ℤ.- 1 ≡ pos (suc k)
          lemma' = ℚ₊.0ℤ<ᵗ→≡possuc (1+a ℤ.· 1+k ℤ.- 1) 0<ᵗak-1

          l : ℕ
          l = fst lemma'
          l≡ak-1 : 1+a ℤ.· 1+k ℤ.- 1 ≡ pos (suc l)
          l≡ak-1 = snd lemma'

          δ : ℚ₊
          δ = [ pos(suc l) , bk ] , tt
          δ<ε : δ <₊ ([ pos(suc a) / 1+ b ] , t)
          δ<ε = subst2 (_<ℚ_)
                (cong [_/ bk ] l≡ak-1)
                (ℚ.·CancelR {pos(suc a)} {1+ b} (1+ k))
                (ℚ.<ℤ→<ℚ (1+a ℤ.· 1+k ℤ.- 1) (1+a ℤ.· 1+k) bk ℤ.predℤ'<)
          x≈[δ]y : x ≈[ δ ]R y
          x≈[δ]y = subst ((ι (1+b ℤ.· 1+k) · abs(x - y) <_) ∘ ι) l≡ak-1 lemma

    -- do syntax with let takes too long to typecheck...
    {-
    do
    k , 1<k[a-b∣x-y∣] ← archimedeanProperty _ _ (0<ι₊₁ 0) (<→0<- _ _ b∣x-y∣<a)

    let
      1+a = pos (suc a) ; 1+b = pos (suc b) ; 1+k = pos (suc k)
      bk = (1+ b) ℕ₊₁.·₊₁ (1+ k)

      step1 = sym $ λ i → pres· 1+a 1+k i + pres- 1 i - pres· 1+b 1+k i · abs(x - y)
      step2 = sym $ congL _-_ (pres+ _ _)

      lemma : ι (1+b ℤ.· 1+k) · abs(x - y) < ι (1+a ℤ.· 1+k ℤ.- 1)
      lemma = 0<-→< _ _ $ flip (subst (0r <_)) (<→0<- _ _ 1<k[a-b∣x-y∣]) $
        ι₊₁ k · (ι₊₁ a - ι₊₁ b · abs(x - y)) - ι₊₁ 0            ≡⟨ solve! RCR ⟩
        ι₊₁ a · ι₊₁ k - ι₊₁ 0 - ι₊₁ b · ι₊₁ k · abs(x - y)      ≡⟨ step1 ⟩
        ι (1+a ℤ.· 1+k) + (ι -1) - ι (1+b ℤ.· 1+k) · abs(x - y) ≡⟨ step2 ⟩
        ι (1+a ℤ.· 1+k ℤ.- 1) - ι (1+b ℤ.· 1+k) · abs(x - y)    ∎

      0<ak-1 : 0 <ℤ (1+a ℤ.· 1+k ℤ.- 1) ℤ.· 1
      0<ak-1 = reflect< 0 ((1+a ℤ.· 1+k ℤ.- 1) ℤ.· 1) $ begin<
        ι 0                          ≡→≤⟨ pres0 ∙ solve! RCR ⟩
        ι (1+b ℤ.· 1+k) · 0r           ≤⟨ ·MonoL≤ _ _ _ (0≤ι₀₊ _) (0≤abs (x - y)) ⟩
        ι (1+b ℤ.· 1+k) · abs(x - y)   <⟨ lemma ⟩
        ι (1+a ℤ.· 1+k ℤ.- 1)        ≡→≤⟨ sym $ cong ι (ℤ.·IdR _) ⟩
        ι ((1+a ·ℤ 1+k -ℤ 1) ·ℤ 1)     ◾

      0<ᵗak-1 : fst (ℚ₊.0ℤ<ᵗ (1+a ℤ.· 1+k ℤ.- 1))
      0<ᵗak-1 = ℚ₊.<→0<ᵗ [ 1+a ℤ.· 1+k ℤ.- 1 , (1+ b) ℕ₊₁.·₊₁ (1+ k) ] 0<ak-1

      l , l≡ak-1 = ℚ₊.0ℤ<ᵗ→≡possuc (1+a ℤ.· 1+k ℤ.- 1) 0<ᵗak-1

      ak-1<ak : 1+a ℤ.· 1+k ℤ.- 1 ℤ.< 1+a ℤ.· 1+k
      ak-1<ak = {! ℤ.<-+o  !}

      δ      = [ pos(suc l) , bk ] , tt
      δ<ε    = subst2 _<ℚ_ (cong [_/ bk ] l≡ak-1) {!   !} {!   !}
      x≈[δ]y = subst ((ι (1+b ℤ.· 1+k) · abs(x - y) <_) ∘ ι) l≡ak-1 lemma
    return (δ , δ<ε , x≈[δ]y)
    -}

  ArchimedeanRing→PremetricSpace : PremetricSpace ℓ ℓ'
  fst ArchimedeanRing→PremetricSpace = R
  _≈[_]_ (snd ArchimedeanRing→PremetricSpace) x ε y = fst (Closeness.≈ₚ x y ε)
  isPremetric (snd ArchimedeanRing→PremetricSpace) = isPM
    where
      open IsPremetric

      isPM : IsPremetric _
      isPM .isSetM        = is-set
      isPM .isProp≈       = isProp≈R
      isPM .isRefl≈       = λ x → uncurry $ SQ.elimProp
        (λ a/b → isPropΠ λ t → snd(Closeness.≈ₚ x x (a/b , t)))
        (uncurry (onFractionsIsRefl≈R x))
      isPM .isSym≈        = λ x y → uncurry $ SQ.elimProp
        (λ a/b → isPropΠ2 λ t _ → snd(Closeness.≈ₚ y x (a/b , t)))
        (uncurry (onFractionsIsSym≈R x y))
      isPM .isSeparated≈  = isSeparated≈R
      isPM .isTriangular≈ = λ x y z → uncurry $ SQ.elimProp
        (λ a/b → isPropΠ4 λ t δ _ _ → snd(Closeness.≈ₚ x z ((a/b , t) +₊ δ)))
        λ (a , b) t → uncurry $ SQ.elimProp
          (λ c/d → isPropΠ3 λ s _ _ → snd(Closeness.≈ₚ x z (([ _ ] , t) +₊ (c/d , s))))
          (uncurry (onFractionsIsTriangular≈R x y z a b t))
      isPM .isRounded≈    = λ x y → uncurry $ SQ.elimProp
        (λ _ → isPropΠ2 λ _ _ → squash₁)
        (uncurry (onFractionsIsRounded≈R x y))
-- -}
