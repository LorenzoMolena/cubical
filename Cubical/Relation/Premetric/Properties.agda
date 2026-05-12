{-
  Properties of Premetric Spaces ; Numbered Lemmas are from
  "Formalising real numbers in homotopy type theory", Gaëtan Gilbert, 2017
-}
module Cubical.Relation.Premetric.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ renaming (_≤_ to _≤ℕ_ ; _<_ to _<ℕ_)
open import Cubical.Data.Rationals as ℚ using ([_/_] ; eq/)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Binary.Order.Poset.Instances.Nat
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Nat
open import Cubical.Relation.Binary.Order.Quoset.Instances.Nat
open import Cubical.Relation.Binary.Order.QuosetReasoning

open import Cubical.Relation.Premetric.Base

private open module N = JoinProperties ℕ≤Pseudolattice
open <-≤-Reasoning ℕ (snd ℕ≤Poset) (snd ℕ<Quoset)
  (λ _ → ℕ.<≤-trans) (λ _ → ℕ.≤<-trans) ℕ.<-weaken
open <-syntax
open ≤-syntax
open ≡-syntax

open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

private
  variable
    ℓ ℓ' : Level

module PremetricTheory (M' : PremetricSpace ℓ ℓ') where
  private
    M = fst M'
  open PremetricStr (snd M')

  subst≈ : ∀ x y {ε δ} → ⟨ ε ⟩₊ ≡ ⟨ δ ⟩₊ → x ≈[ ε ] y → x ≈[ δ ] y
  subst≈ x y = subst (x ≈[_] y) ∘ ℚ₊≡

  subst≈L : ∀ {x y z ε} → x ≡ y → x ≈[ ε ] z → y ≈[ ε ] z
  subst≈L = subst (_≈[ _ ] _)

  subst≈R : ∀ {x y z ε} → y ≡ z → x ≈[ ε ] y → x ≈[ ε ] z
  subst≈R = subst (_ ≈[ _ ]_)

  isMonotone≈< : ∀ {x y ε δ} → ε <₊ δ → x ≈[ ε ] y → x ≈[ δ ] y
  isMonotone≈< {x} {y} {ε} {δ} ε<δ x≈y = subst≈ x y (minusPlus₊ δ ε) $
    isTriangular≈ x x y [ δ -₊ ε ]⟨ ε<δ ⟩ ε (isRefl≈ x [ δ -₊ ε ]⟨ ε<δ ⟩) x≈y

  isMonotone≈≤ : ∀ {x y ε δ} → ε ≤₊ δ → x ≈[ ε ] y → x ≈[ δ ] y
  isMonotone≈≤ {x} {y} {ε} {δ} ε≤δ x≈y with ⟨ ε ⟩₊ ℚ.≟ ⟨ δ ⟩₊
  ... | lt ε<δ = isMonotone≈< ε<δ x≈y
  ... | eq ε≡δ = subst≈ x y ε≡δ x≈y
  ... | gt δ<ε = ⊥.rec (ℚ.isIrrefl< ⟨ ε ⟩₊ (ℚ.isTrans≤< ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟨ ε ⟩₊ ε≤δ δ<ε))

  module PremetricReasoning where

    private
      variable
        x y z w : M
        ε δ η θ κ : ℚ₊

      +≈ : x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε +₊ δ ] z
      +≈ = isTriangular≈ _ _ _ _ _

      data _≈_≈_[_:+_] (x y z : M) (δ η : ℚ₊) : Type (ℓ-max ℓ ℓ') where
        ≈step+ : x ≈[ δ ] y → y ≈[ η ] z → x ≈ y ≈ z [ δ :+ η ]
        ≈end   : x ≡ y      → y ≡ z      → x ≈ y ≈ z [ δ :+ η ]

      is≈Step+ : x ≈ y ≈ z [ δ :+ η ] → Type
      is≈Step+ (≈step+ _ _) = Unit
      is≈Step+ (≈end   _ _) = ⊥.⊥

      step+₊ : x ≈ y ≈ z [ δ :+ η ] → ℚ₊ → ℚ₊ → ℚ₊
      step+₊ (≈step+ _ _) = _+₊_
      step+₊ (≈end   _ _) = const

    infixr 2 step≈
    step≈ : ∀ x {w} ε {δ η}
          → (r : y ≈ z ≈ w [ δ :+ η ])
          → x ≈[ ε ] y
          → x ≈ z ≈ w [ step+₊ r ε δ :+ η ]
    step≈ x ε (≈step+ y≈ ≈w) x≈ = ≈step+ (+≈ x≈ y≈) ≈w
    step≈ x ε (≈end   y≡ ≡w) x≈ = ≈step+ (subst≈R y≡ x≈) (subst≈R ≡w (isRefl≈ _ _))

    syntax step≈ x ε y≈w x≈y = x ≈[ ε ]⟨ x≈y ⟩ y≈w

    infixr 2 step≈≡
    step≈≡ : ∀ x {w} ε {θ δ η}
           → ⟨ θ ⟩₊ ≡ ⟨ ε ⟩₊
           → (r : y ≈ z ≈ w [ δ :+ η ])
           → x ≈[ θ ] y
           → x ≈ z ≈ w [ step+₊ r ε δ :+ η ]
    step≈≡ x ε θ≡ε r = step≈ x ε r ∘ subst≈ x _ θ≡ε

    syntax step≈≡ x ε θ≡ε y≈w x≈y = x ≈≡[ ε ]⟨ θ≡ε ⟩⟨ x≈y ⟩ y≈w

    infixr 2 step≈<
    step≈< : ∀ x {w} ε {θ δ η}
           → θ <₊ ε
           → (r : y ≈ z ≈ w [ δ :+ η ])
           → x ≈[ θ ] y
           → x ≈ z ≈ w [ step+₊ r ε δ :+ η ]
    step≈< x ε θ<ε r = step≈ x ε r ∘ isMonotone≈< θ<ε

    syntax step≈< x ε θ<ε y≈w x≈y = x ≈<[ ε ]⟨ θ<ε ⟩⟨ x≈y ⟩ y≈w

    infixr 2 step≈≤
    step≈≤ : ∀ x {w} ε {θ δ η}
           → θ ≤₊ ε
           → (r : y ≈ z ≈ w [ δ :+ η ])
           → x ≈[ θ ] y
           → x ≈ z ≈ w [ step+₊ r ε δ :+ η ]
    step≈≤ x ε θ≤ε r = step≈ x ε r ∘ isMonotone≈≤ θ≤ε

    syntax step≈≤ x ε θ≤ε y≈w x≈y = x ≈≤[ ε ]⟨ θ≤ε ⟩⟨ x≈y ⟩ y≈w

    infix 3 ≈⁻_
    ≈⁻_ : x ≈[ ε ] y → y ≈[ ε ] x
    ≈⁻_ = isSym≈ _ _ _

    infixr 2 step≡→≈
    step≡→≈ : ∀ x {w} {δ η}
            → (r : y ≈ z ≈ w [ δ :+ η ])
            → x ≡ y
            → x ≈ z ≈ w [ δ :+ η ]
    step≡→≈ x (≈step+ y≈ ≈w) x≡ = ≈step+ (subst≈L (sym x≡) y≈) ≈w
    step≡→≈ x (≈end   y≡ ≡w) x≡ = ≈end (x≡ ∙ y≡) ≡w

    syntax step≡→≈ x y≈w x≡y = x ≡→≈⟨ x≡y ⟩ y≈w

    infix 3 _≈∎
    _≈∎ : ∀ x → x ≈ x ≈ x [ 1 :+ 1 ] -- dummy ℚ₊ values, discarded by ≈end/const
    _≈∎ x = ≈end refl refl

    infix 1 begin≈[_]⟨_⟩_
    begin≈[_]⟨_⟩_ : ∀ ε {δ} {x y} → ⟨ δ ⟩₊ ≡ ⟨ ε ⟩₊
                 → (r : x ≈ y ≈ y [ δ :+ 1 ])
                 → {is≈Step+ r}
                 → x ≈[ ε ] y
    begin≈[ ε ]⟨ p ⟩ ≈step+ x≈y _ = subst≈ _ _ p x≈y

    infix 1 begin≈[_]⟨⟩_
    begin≈[_]⟨⟩_ : ∀ ε {x y}
                → (r : x ≈ y ≈ y [ ε :+ 1 ])
                → {is≈Step+ r}
                → x ≈[ ε ] y
    begin≈[ ε ]⟨⟩ ≈step+ x≈y _ = x≈y

  open PremetricReasoning

  -- Cauchy Approximations/Sequences

  isCauchy : (ℚ₊ → M) → Type ℓ'
  isCauchy x = ∀ (ε δ : ℚ₊) → x ε ≈[ ε +₊ δ ] x δ

  isCauchySeqΣ : (ℕ → M) → Type ℓ'
  isCauchySeqΣ x = (ε : ℚ₊) → Σ[ N ∈ ℕ ] ∀ m n → N ≤ℕ m → N ≤ℕ n → x m ≈[ ε ] x n

  isCauchySeq : (ℕ → M) → Type ℓ'
  isCauchySeq x = (ε : ℚ₊) → ∃[ N ∈ ℕ ] ∀ m n → N ≤ℕ m → N ≤ℕ n → x m ≈[ ε ] x n

  isPropIsCauchySeq : ∀ x → isProp (isCauchySeq x)
  isPropIsCauchySeq _ = isPropΠ λ _ → squash₁

  isCauchySeqΣ→isCauchySeq : ∀ x → isCauchySeqΣ x → isCauchySeq x
  isCauchySeqΣ→isCauchySeq _ = ∣_∣₁ ∘_

  isCauchySeqΣ< : (ℕ → M) → Type ℓ'
  isCauchySeqΣ< x = (ε : ℚ₊) → Σ[ N ∈ ℕ ] ∀ m n → N ≤ℕ m → m <ℕ n → x m ≈[ ε ] x n

  isCauchySeq< : (ℕ → M) → Type ℓ'
  isCauchySeq< x = (ε : ℚ₊) → ∃[ N ∈ ℕ ] ∀ m n → N ≤ℕ m → m <ℕ n → x m ≈[ ε ] x n

  isPropIsCauchySeq< : ∀ x → isProp (isCauchySeq< x)
  isPropIsCauchySeq< _ = isPropΠ λ _ → squash₁

  isCauchySeqΣ<→isCauchySeq< : ∀ x → isCauchySeqΣ< x → isCauchySeq< x
  isCauchySeqΣ<→isCauchySeq< _ = ∣_∣₁ ∘_

  -- this formalizes "WLOG assume m < n"
  module SeqΣWLOG<
    (x : ℕ → M) (ε : ℚ₊) (cs< : Σ[ N ∈ ℕ ] ∀ m n → N ≤ℕ m → m <ℕ n → x m ≈[ ε ] x n) where

    go : Σ[ N ∈ ℕ ] ∀ m n → N ≤ℕ m → N ≤ℕ n → x m ≈[ ε ] x n
    go .fst = fst cs<
    go .snd m n N≤m N≤n with m ℕ.≟ n
    ... | lt m<n = snd cs< m n N≤m m<n
    ... | eq m≡n = subst ((x m ≈[ ε ]_) ∘ x) m≡n (isRefl≈ (x m) ε)
    ... | gt n<m = isSym≈ (x n) (x m) ε (snd cs< n m N≤n n<m)

  isCauchySeqΣ<→isCauchySeqΣ : ∀ x → isCauchySeqΣ< x → isCauchySeqΣ x
  isCauchySeqΣ<→isCauchySeqΣ x icsΣ< ε = SeqΣWLOG<.go x ε (icsΣ< ε)

  isCauchySeq<→isCauchySeq : ∀ x → isCauchySeq< x → isCauchySeq x
  isCauchySeq<→isCauchySeq x ics< ε = PT.map (SeqΣWLOG<.go x ε) (ics< ε)

  isCauchySeqΣ→isCauchySeqΣ< : ∀ x → isCauchySeqΣ x → isCauchySeqΣ< x
  isCauchySeqΣ→isCauchySeqΣ< x icsΣ ε .fst = fst (icsΣ ε)
  isCauchySeqΣ→isCauchySeqΣ< x icsΣ ε .snd m n N≤m m<n = snd (icsΣ ε) m n N≤m $ begin≤
    fst (icsΣ ε) ≤⟨ N≤m ⟩ m <⟨ m<n ⟩ n ◾

  isCauchySeq→isCauchySeq< : ∀ x → isCauchySeq x → isCauchySeq< x
  isCauchySeq→isCauchySeq< x ics ε = PT.map
    (λ (N , cs) → N , λ m n N≤m m<n → cs m n N≤m $ begin≤ N ≤⟨ N≤m ⟩ m <⟨ m<n ⟩ n ◾)
    (ics ε)

  isCauchySeqΣ→isCauchy : ∀ x → isCauchySeqΣ x → Σ[ y ∈ (ℚ₊ → M) ] isCauchy y
  isCauchySeqΣ→isCauchy x icsΣ .fst = x ∘ fst ∘ icsΣ
  isCauchySeqΣ→isCauchy x icsΣ .snd = λ ε δ → let N = fst ∘ icsΣ in
    begin≈[ ε +₊ δ ]⟨⟩
    x (N ε)               ≈[ ε ]⟨ snd (icsΣ ε) _ _ (ℕ.≤-refl) (N.L≤∨ {N ε}) ⟩
    x (ℕ.max (N ε) (N δ)) ≈[ δ ]⟨ snd (icsΣ δ) _ _ (N.R≤∨ {N ε}) (ℕ.≤-refl) ⟩
    x (N δ)               ≈∎

  isCauchySeqΣ<→isCauchy : ∀ x → isCauchySeqΣ< x → Σ[ y ∈ (ℚ₊ → M) ] isCauchy y
  isCauchySeqΣ<→isCauchy x = isCauchySeqΣ→isCauchy x ∘ isCauchySeqΣ<→isCauchySeqΣ x

  isLimit : (ℚ₊ → M) → M → Type ℓ'
  isLimit x l = ∀ ε θ → x ε ≈[ ε +₊ θ ] l

  isPropIsLimit : ∀ x l → isProp (isLimit x l)
  isPropIsLimit x l = isPropΠ2 λ ε δ → isProp≈ (x ε) l (ε +₊ δ)

  limit : (ℚ₊ → M) → Type (ℓ-max ℓ ℓ')
  limit x = Σ[ l ∈ M ] isLimit x l

  isPropLimit : ∀ x → isProp (limit x)
  isPropLimit x (l , l-lim) (l' , l'-lim) = Σ≡Prop (isPropIsLimit x) $
    isSeparated≈ l l' λ ε → begin≈[ ε ]⟨ /2+/2≡id ⟨ ε ⟩₊ ⟩
      l         ≈≡[ ε /2₊ ]⟨ /4+/4≡/2 ⟨ ε ⟩₊ ⟩⟨ ≈⁻ l-lim (ε /4₊) (ε /4₊) ⟩
      x (ε /4₊) ≈≡[ ε /2₊ ]⟨ /4+/4≡/2 ⟨ ε ⟩₊ ⟩⟨   l'-lim (ε /4₊) (ε /4₊) ⟩
      l'        ≈∎

  isComplete : Type (ℓ-max ℓ ℓ')
  isComplete = ∀ x → isCauchy x → limit x

  isPropIsComplete : isProp isComplete
  isPropIsComplete = isPropΠ λ _ → isProp→ (isPropLimit _)

  isLimit≈< : ∀ x l → isLimit x l → ∀ ε δ → (ε <₊ δ) → x ε ≈[ δ ] l
  isLimit≈< x l l-lim ε δ ε<δ = begin≈[ δ ]⟨ ℚ.+Comm ⟨ ε ⟩₊ (δ -₊ ε) ∙ minusPlus₊ δ ε ⟩
    x ε ≈[ ε +₊ [ δ -₊ ε ]⟨ ε<δ ⟩ ]⟨ l-lim ε [ δ -₊ ε ]⟨ ε<δ ⟩ ⟩
    l   ≈∎

  -- Lemma 2.8
  isLim≈+ : ∀ u x l ε δ → isLimit x l → u ≈[ δ ] x ε → u ≈[ ε +₊ δ ] l
  isLim≈+ u x l ε δ l-lim = PT.rec (isProp≈ u l _)
    (λ (η , η<δ , u≈xε) →
    begin≈[ ε +₊ δ ]⟨
      ℚ.+Comm ⟨ η ⟩₊ _ ∙
      sym (ℚ.+Assoc ⟨ ε ⟩₊ (δ -₊ η) ⟨ η ⟩₊) ∙
      cong (⟨ ε ⟩₊ ℚ.+_) (minusPlus₊ δ η) ⟩
      u    ≈[ η ]⟨ u≈xε ⟩
      x ε  ≈[ ε +₊ [ δ -₊ η ]⟨ η<δ ⟩ ]⟨ l-lim ε [ δ -₊ η ]⟨ η<δ ⟩ ⟩
      l    ≈∎)
    ∘ isRounded≈ u (x ε) δ

  isLim≈- : ∀ u x l ε δ Δ → isLimit x l → u ≈[ ε -₊ δ , Δ ] x δ → u ≈[ ε ] l
  isLim≈- u x l ε δ Δ l-lim =
    subst≈ u l (ℚ.+Comm ⟨ δ ⟩₊ _ ∙ minusPlus₊ ε δ) ∘ isLim≈+ u x l δ (ε -₊ δ , Δ) l-lim

  -- Lemma 2.9
  isLim≈+₂ : ∀ x y l l' ε δ η → isLimit x l → isLimit y l'
           → x δ ≈[ ε ] y η → l ≈[ δ +₊ (η +₊ ε) ] l'
  isLim≈+₂ x y l l' ε δ η l-lim l'-lim =
      isSym≈ l' l (δ +₊ (η +₊ ε))
    ∘ isLim≈+ l' x l δ (η +₊ ε) l-lim
    ∘ isSym≈ (x δ) l' (η +₊ ε)
    ∘ isLim≈+ (x δ) y l' η ε l'-lim

  isLim≈-₂ : ∀ x y l l' ε δ η Δ → isLimit x l → isLimit y l'
           → x δ ≈[ ε -₊ (δ +₊ η) , Δ ] y η → l ≈[ ε ] l'
  isLim≈-₂ x y l l' ε δ η Δ l-lim l'-lim = subst≈ l l'
    (⟨ δ +₊ (η +₊ (ε -₊ (δ +₊ η) , Δ)) ⟩₊ ≡⟨ ℚ.+Assoc ⟨ δ ⟩₊ ⟨ η ⟩₊ _ ⟩
    ⟨ δ +₊ η ⟩₊ ℚ.+ (ε -₊ (δ +₊ η))       ≡⟨ ℚ.+Comm ⟨ δ +₊ η ⟩₊ _ ⟩
    (ε -₊ (δ +₊ η)) ℚ.+ ⟨ δ +₊ η ⟩₊       ≡⟨ minusPlus₊ ε (δ +₊ η) ⟩
    ⟨ ε ⟩₊                                ∎)
    ∘ isLim≈+₂ x y l l' (ε -₊ (δ +₊ η) , Δ) δ η l-lim l'-lim
