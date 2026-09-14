module Cubical.Data.Nat.BinarySearch where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Mod renaming (quotient_/_ to _/_ ; remainder_/_ to _%_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    P : ℕ → Type ℓ

open Minimal hiding (search ; →Least)

module IncreasingDec (dec : ∀ n → Dec (P n)) (P≤ : ∀ {m n} → m ≤ᵗ n → P m → P n) where

  mid : ℕ → ℕ → ℕ
  mid a Δ = Δ / 2 + suc a

  private
    ¬P> : ∀ {m n} → m <ᵗ n → ¬ P n → ¬ P m
    ¬P> {m} m<n ¬Pn = ¬Pn ∘_ $ P≤ $ <ᵗ-weaken {m} $ m<n

    sum≤gap/2+mid : ∀ {a} Δ → Δ + a ≤ᵗ Δ / 2 + mid a Δ
    sum≤gap/2+mid {a} Δ = ≤→≤ᵗ $
      subst (Δ + a ≤_) (sym $ +-assoc (Δ / 2) _ (suc a) ∙ +-suc _ a) (≤-+ʳ (≤1+/2+/2 Δ))

    -- lemma needed to pass termination checking
    ≤ᵗf : ∀ {Δ f} → Δ ≤ᵗ f → suc Δ / 2 ≤ᵗ f
    ≤ᵗf {Δ} {f} = <ᵗ≤ᵗ-trans {suc Δ / 2} {suc Δ} {suc f} (<→<ᵗ (quotient<id Δ 0))

    helper : ∀ a Δ f → Δ ≤ᵗ f → ¬ (P a) → P (Δ + a) → Σ[ m ∈ ℕ ] Least P m
    helper a zero    f       _   ¬Pa Pa     = ⊥.rec (¬Pa Pa)
    helper a Δ@(suc Δ') (suc f) Δ≤f ¬Pa PΔ+a with dec (suc a)
    ... | yes P1+a = (suc a) , P1+a , λ _ → (¬Pa ∘_) ∘ P≤
    ... | no ¬P1+a with dec (mid a Δ)
    ... | yes Pm =
      helper (suc a)   (Δ / 2) f (≤ᵗf {Δ'} Δ≤f) ¬P1+a Pm
    ... | no ¬Pm =
      helper (mid a Δ) (Δ / 2) f (≤ᵗf {Δ'} Δ≤f) ¬Pm (P≤ (sum≤gap/2+mid Δ) PΔ+a)

  -- if for a : ℕ we know already know that ¬ P a, then we can start searching from there

  search[_,_] : ∀ a n → a ≤ n → ¬ P a → (Σ[ m ∈ ℕ ] Least P m) ⊎ (∀ m → m <ᵗ n → ¬ P m)
  search[ a , n ] (Δ , Δ+a≡n) ¬Pa with dec (Δ + a)
  ... | yes Pn = inl (helper a Δ Δ (≤ᵗ-refl Δ) ¬Pa Pn)
  ... | no ¬Pn = inr (λ _ → flip ¬P> (¬Pn ∘ subst P (sym Δ+a≡n)))

  →Least[_,_] : ∀ a n → a ≤ n → ¬ P a → P n → Σ ℕ (Least P)
  →Least[ a , n ] (Δ , Δ+a≡n) ¬Pa Pn =
    helper a Δ Δ (≤ᵗ-refl Δ) ¬Pa (subst P (sym Δ+a≡n) Pn)

  -- otherwise, we can start at zero, relying on the decidability of P 0

  search : ∀ n → (Σ[ m ∈ ℕ ] Least P m) ⊎ (∀ m → m <ᵗ n → ¬ P m)
  search n with dec 0
  ... | yes P0 = inl (0 , P0 , λ _ b _ → b)
  ... | no ¬P0 = search[ 0 , n ] zero-≤ ¬P0

  →Least : Σ _ P → Σ _ (Least P)
  →Least (n , Pn) with search n
  ... | inl least = least
  ... | inr ¬P<n  = n , Pn , ¬P<n

-- one application is to search the biggest image of
-- an increasing function which is below a given k : ℕ
module BiggestImage≤ (f : ℕ → ℕ) (inc : isIncreasing f) (f0=0 : f 0 ≡ 0) (k : ℕ) where
  open IncreasingDec
    ((k <ᵗ?_) ∘ f ∘ suc)
    (λ {m} {n} → flip (<ᵗ≤ᵗ-trans {k} {f (suc m)} {f (suc n)}) ∘ ≤→≤ᵇ ∘ inc ∘ ≤ᵇ→≤)
    public hiding (mid)

  module _ (ΣP : Σ[ n ∈ ℕ ] k <ᵗ f (suc n)) where
    biggestImage≤ : ℕ
    biggestImage≤ = fst (→Least ΣP)

    <funSuc : k < f (suc biggestImage≤)
    <funSuc = <ᵗ→< $ fst $ snd $ →Least ΣP

    fun≤ : f biggestImage≤ ≤ k
    fun≤ with →Least ΣP
    ... | zero  , k<fsn , r<n→¬k<fsr = subst (_≤ k) (sym f0=0) zero-≤
    ... | suc r , k<fsn , r<n→¬k<fsr = <-asym' $ r<n→¬k<fsr r (<ᵗsuc {r}) ∘ <→<ᵗ

-- as an example, we can implement the floor of the square root on natural numbers;
-- as shown below, the use of binary search makes the implementation reasonably efficient
module example where
  _² = ∘diag _·_

  ≤→≤² : ∀ {m n} → m ≤ n → m ² ≤ n ²
  ≤→≤² {zero}  {n}     = λ _ → zero-≤
  ≤→≤² {suc m} {zero}  = ⊥.rec ∘ ¬-<-zero
  ≤→≤² {suc m} {suc n} = λ m≤n → ≤-trans (≤-·ˡ {k = suc m} m≤n) (≤-·ʳ {k = suc n} m≤n)

  id≤² : ∀ n → n ≤ n ²
  id≤²    zero   = zero-≤
  id≤² n@(suc _) = subst (_≤ n · n) (·-identityʳ n) (≤-·ˡ {k = n} (suc-≤-suc zero-≤))

  Σ<suc² : ∀ n → Σ[ k ∈ ℕ ] n <ᵗ (suc k) ²
  Σ<suc² n = (n , <→<ᵗ (id≤² (suc n)))

  open BiggestImage≤ _² ≤→≤² refl

  ⌊√_⌋ : ℕ → ℕ
  ⌊√ n ⌋ = biggestImage≤ n (Σ<suc² n)

  <⌊√1+_⌋ : ∀ n → n < suc ⌊√ n ⌋ ²
  <⌊√1+ n ⌋ = <funSuc n (Σ<suc² n)

  ⌊√_⌋≤ : ∀ n → ⌊√ n ⌋ ² ≤ n
  ⌊√ n ⌋≤ = fun≤ n (Σ<suc² n)

  √2Digits : ℕ → ℕ × ℕ
  √2Digits n = toDigits n ⌊√ 2 · 100 ^ n ⌋ where
    toDigits : ℕ → ℕ → ℕ × ℕ
    toDigits n x = (x / (10 ^ n) , x % (10 ^ n))

  _ : ⌊√ 64 ⌋ ≡ 8
  _ = refl

  _ : ⌊√ 63 ⌋ ≡ 7
  _ = refl

  _ : ⌊√ 65 ⌋ ≡ 8
  _ = refl

  _ : √2Digits 20 ≡ (1 , 41421356237309504880)
  _ = refl
