module Cubical.Relation.Premetric.Instances.FunctionSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP using (⟨_⟩ ; str)

open import Cubical.Data.Sigma

open import Cubical.Data.Rationals.Fast.Properties as ℚ using ()
open import Cubical.Data.Rationals.Fast.Order as ℚOrd using () renaming (_<_ to _<ℚ_)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings

open OrderedCommRingStr (str ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

private
  variable
    ℓA ℓM ℓM' ℓN ℓN' : Level

module _ {ℓA ℓN ℓN'} (A : Type ℓA) (N' : PremetricSpace ℓN ℓN') where
  private
    N = ⟨ N' ⟩
    module PN = PremetricStr (snd N')
    module NTh = PremetricTheory N'

  infix 5 _≈→[_]_

  _≈→[_]_ : (A → N) → ℚ₊ → (A → N) → Type (ℓ-max ℓA ℓN')
  f ≈→[ ε ] g = ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (∀ x → f x PN.≈[ δ ] g x)

  ≈→→pointwise : ∀ f g ε → f ≈→[ ε ] g → ∀ x → f x PN.≈[ ε ] g x
  ≈→→pointwise f g ε =
    PT.rec (isPropΠ λ x → PN.isProp≈ (f x) (g x) ε) λ where
      (δ , δ<ε , pw) x → PN.isMonotone≈< (f x) (g x) δ ε δ<ε (pw x)

  isPremetric→ : IsPremetric _≈→[_]_
  isPremetric→ .IsPremetric.isSetM = isSet→ PN.isSetM
  isPremetric→ .IsPremetric.isProp≈ _ _ _ = squash₁
  isPremetric→ .IsPremetric.isRefl≈ f ε =
    ∣ (ε /2₊ , /2₊<id ε , λ x → PN.isRefl≈ (f x) (ε /2₊)) ∣₁
  isPremetric→ .IsPremetric.isSym≈ f g ε =
    PT.rec squash₁ λ where
      (δ , δ<ε , pw) → ∣ (δ , δ<ε , λ x → PN.isSym≈ (f x) (g x) δ (pw x)) ∣₁
  isPremetric→ .IsPremetric.isSeparated≈ f g f≈g =
    funExt λ x → PN.isSeparated≈ (f x) (g x) λ ε → ≈→→pointwise f g ε (f≈g ε) x
  isPremetric→ .IsPremetric.isTriangular≈ f g h ε θ =
    PT.rec (isProp→ squash₁) λ where
      (δ₁ , δ₁<ε , fg) →
        PT.rec squash₁ λ where
          (δ₂ , δ₂<θ , gh) →
            ∣ (δ₁ +₊ δ₂
            , +Mono< ⟨ δ₁ ⟩₊ ⟨ ε ⟩₊ ⟨ δ₂ ⟩₊ ⟨ θ ⟩₊ δ₁<ε δ₂<θ
            , λ x → PN.isTriangular≈ (f x) (g x) (h x) δ₁ δ₂ (fg x) (gh x))
            ∣₁
  isPremetric→ .IsPremetric.isRounded≈ f g ε =
    PT.rec squash₁ λ where
      (δ₁ , δ₁<ε , pw) →
        let
          gap = [ ε -₊ δ₁ ]⟨ δ₁<ε ⟩
          δ = δ₁ +₊ gap /2₊

          δ<ε : δ <₊ ε
          δ<ε = subst2 (λ x y → x <ℚ y)
            (ℚ.+Comm ⟨ gap /2₊ ⟩₊ ⟨ δ₁ ⟩₊)
            (minusPlus₊ ε δ₁)
            (+MonoR< ⟨ gap /2₊ ⟩₊ ⟨ gap ⟩₊ ⟨ δ₁ ⟩₊ (/2₊<id gap))

          δ₁<δ : δ₁ <₊ δ
          δ₁<δ = <₊SumLeft δ₁ (gap /2₊)
        in
        ∣ (δ , δ<ε , ∣ (δ₁ , δ₁<δ , pw) ∣₁) ∣₁

  →PremetricSpace : PremetricSpace (ℓ-max ℓA ℓN) (ℓ-max ℓA ℓN')
  fst →PremetricSpace = A → N
  snd →PremetricSpace = premetricstr _≈→[_]_ isPremetric→

  module FTh = PremetricTheory →PremetricSpace

  isComplete→ : NTh.isComplete → FTh.isComplete
  isComplete→ N-complete s s-cauchy = l , l-lim
    where
    pointwiseCauchy : ∀ x → NTh.isCauchy (λ ε → s ε x)
    pointwiseCauchy x ε θ =
      ≈→→pointwise (s ε) (s θ) (ε +₊ θ) (s-cauchy ε θ) x

    l : A → N
    l x = fst (N-complete (λ ε → s ε x) (pointwiseCauchy x))

    l-lim-pointwise : ∀ x → NTh.isLimit (λ ε → s ε x) (l x)
    l-lim-pointwise x = snd (N-complete (λ ε → s ε x) (pointwiseCauchy x))

    l-lim : FTh.isLimit s l
    l-lim ε θ =
      ∣ (ε +₊ θ /2₊
      , subst2 (λ x y → x <ℚ y)
          (ℚ.+Comm ⟨ θ /2₊ ⟩₊ ⟨ ε ⟩₊)
          (ℚ.+Comm ⟨ θ ⟩₊ ⟨ ε ⟩₊)
          (+MonoR< ⟨ θ /2₊ ⟩₊ ⟨ θ ⟩₊ ⟨ ε ⟩₊ (/2₊<id θ))
      , λ x → l-lim-pointwise x ε (θ /2₊))
      ∣₁

module _ {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where
  private
    M = ⟨ M' ⟩
    N = ⟨ N' ⟩
    module PM = PremetricStr (snd M')
    module PN = PremetricStr (snd N')
    module NTh' = PremetricTheory N'
    module FTh' = PremetricTheory (→PremetricSpace M N')

  limLipschitz :
    (N-complete : NTh'.isComplete) (L : ℚ₊)
    → (s : ℚ₊ → (M → N)) (s-cauchy : FTh'.isCauchy s)
    → (∀ ε → IsLipschitzWith (snd M') (s ε) (snd N') L)
    → IsLipschitzWith (snd M') (fst (isComplete→ M N' N-complete s s-cauchy)) (snd N') L
  limLipschitz N-complete L s s-cauchy L-lip = islipschitzwith λ x y ε x≈y →
    PT.rec (PN.isProp≈ (l x) (l y) (L ·₊ ε)) (step x y ε) (PM.isRounded≈ x y ε x≈y)
    where
    l : M → N
    l = fst (isComplete→ M N' N-complete s s-cauchy)

    l-lim : FTh'.isLimit s l
    l-lim = snd (isComplete→ M N' N-complete s s-cauchy)

    l-lim-pointwise : ∀ z → NTh'.isLimit (λ ρ → s ρ z) (l z)
    l-lim-pointwise z ρ θ =
      ≈→→pointwise M N' (s ρ) l (ρ +₊ θ) (l-lim ρ θ) z

    step : ∀ x y ε → Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x PM.≈[ δ ] y) → l x PN.≈[ L ·₊ ε ] l y
    step x y ε (δ , δ<ε , x≈δy) =
      PN.isRounded≈⁻ (l x) (l y) (L ·₊ ε)
        ∣ (η +₊ (η +₊ L ·₊ δ)
        , η+η+Lδ<Lε
        , NTh'.isLim≈+₂
            (λ ρ → s ρ x) (λ ρ → s ρ y) (l x) (l y)
            (L ·₊ δ) η η
            (l-lim-pointwise x)
            (l-lim-pointwise y)
            (IsLipschitzWith.pres≈ (L-lip η) x y δ x≈δy))
        ∣₁
      where
      Lδ<Lε : (L ·₊ δ) <₊ (L ·₊ ε)
      Lδ<Lε = ·MonoL< ⟨ δ ⟩₊ ⟨ ε ⟩₊ ⟨ L ⟩₊ (snd L) δ<ε

      gap : ℚ₊
      gap = [ (L ·₊ ε) -₊ (L ·₊ δ) ]⟨ Lδ<Lε ⟩

      η : ℚ₊
      η = gap /4₊

      η+η+Lδ<Lε : η +₊ (η +₊ L ·₊ δ) <₊ L ·₊ ε
      η+η+Lδ<Lε = begin<
        ⟨ η +₊ (η +₊ L ·₊ δ) ⟩₊         ≡→≤⟨ ℚ.+Assoc ⟨ η ⟩₊ ⟨ η ⟩₊ ⟨ L ·₊ δ ⟩₊ ⟩
        ⟨ η +₊ η ⟩₊ ℚ.+ ⟨ L ·₊ δ ⟩₊     ≡→≤⟨ cong (ℚ._+ ⟨ L ·₊ δ ⟩₊) (/4+/4≡/2 ⟨ gap ⟩₊) ⟩
        ⟨ gap /2₊ +₊ L ·₊ δ ⟩₊          <⟨ +MonoR< ⟨ gap /2₊ ⟩₊ ⟨ gap ⟩₊ ⟨ L ·₊ δ ⟩₊ (/2₊<id gap) ⟩
        ⟨ gap ⟩₊ ℚ.+ ⟨ L ·₊ δ ⟩₊         ≡→≤⟨ minusPlus₊ (L ·₊ ε) (L ·₊ δ) ⟩
        ⟨ L ·₊ ε ⟩₊                      ◾
