module Cubical.Relation.Premetric.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP


open import Cubical.Data.Sigma

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ renaming (_≤_ to _≤ℕ_ ; _<_ to _<ℕ_)
open import Cubical.Data.NatPlusOne as ℕ₊₁ using ()
open import Cubical.Data.Int.Fast as ℤ using ()
open import Cubical.Data.Rationals.Fast as ℚ using ([_/_] ; eq/)

open import Cubical.Relation.Binary.Order.Poset.Instances.Nat
open import Cubical.Relation.Binary.Order.Quoset.Instances.Nat
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Nat
open module N = JoinProperties ℕ≤Pseudolattice

open import Cubical.Relation.Binary.Order.QuosetReasoning
open <-≤-Reasoning ℕ (str ℕ≤Poset) (str ℕ<Quoset)
  (λ _ → ℕ.<≤-trans) (λ _ → ℕ.≤<-trans) ℕ.<-weaken
open <-syntax
open ≤-syntax
open ≡-syntax

open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast
open OrderedCommRingTheory (ℚOrderedCommRing)
open Charactersitic≠2 ℚOrderedCommRing [ 1 / 2 ] (eq/ _ _ refl)

open import Cubical.Relation.Premetric.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

module PremetricTheory (M' : PremetricSpace ℓ ℓ') where
  M = fst M'
  open PremetricStr (snd M')

  -- Cauchy Approximations/Sequences

  isCauchy : (ℚ₊ → M) → Type ℓ'
  isCauchy x = ∀ (ε δ : ℚ₊) → x ε ≈[ ε +₊ δ ] x δ

  isCauchySeq : (ℕ → M) → Type ℓ'
  isCauchySeq x = Σ[ N ∈ (ℚ₊ → ℕ) ] (∀ ε m n → N ε ≤ℕ m → N ε ≤ℕ n → x m ≈[ ε ] x n)

  isCauchySeq< : (ℕ → M) → Type ℓ'
  isCauchySeq< x = Σ[ N ∈ (ℚ₊ → ℕ) ] (∀ ε m n → m <ℕ n → N ε ≤ℕ m → x m ≈[ ε ] x n)

  isCauchySeq→isCauchy : ∀ x → isCauchySeq x → Σ[ y ∈ (ℚ₊ → M) ] isCauchy y
  isCauchySeq→isCauchy x (N , N≤→≈) .fst ε   = x (N ε)
  isCauchySeq→isCauchy x (N , N≤→≈) .snd ε δ =
    isTriangular≈ _ (x (ℕ.max (N ε) (N δ))) _ ε δ
    (N≤→≈ ε (N ε) (ℕ.max (N ε) (N δ)) (ℕ.≤-refl) (N.L≤∨ {N ε}))
    (N≤→≈ δ (ℕ.max (N ε) (N δ)) (N δ) (N.R≤∨ {N ε}) (ℕ.≤-refl))

  -- this formalizes "WLOG assume m < n"
  isCauchySeq<→isCauchySeq : ∀ x → isCauchySeq< x → isCauchySeq x
  isCauchySeq<→isCauchySeq x (N , xcs<) .fst = N
  isCauchySeq<→isCauchySeq x (N , xcs<) .snd ε m n with m ℕ.≟ n
  ... | lt m<n = λ N≤m _   → xcs< ε m n m<n N≤m
  ... | eq m≡n = λ _   _   → subst ((x m ≈[ ε ]_) ∘ x) m≡n (isRefl≈ _ ε)
  ... | gt m>n = λ _   N≤n → isSym≈ _ _ ε $ xcs< ε n m m>n N≤n

  isCauchySeq→isCauchySeq< : ∀ x → isCauchySeq x → isCauchySeq< x
  isCauchySeq→isCauchySeq< x (N , xcs) .fst = N
  isCauchySeq→isCauchySeq< x (N , xcs) .snd ε m n m<n N≤m = xcs ε m n N≤m $ begin≤
    N ε ≤⟨ N≤m ⟩ m <⟨ m<n ⟩ n ◾

  isCauchySeq<→isCauchy : ∀ x → isCauchySeq< x → Σ[ y ∈ (ℚ₊ → M) ] isCauchy y
  isCauchySeq<→isCauchy x = isCauchySeq→isCauchy x ∘ isCauchySeq<→isCauchySeq x

  isLimit : (ℚ₊ → M) → M → Type ℓ'
  isLimit x l = ∀ ε θ → x ε ≈[ ε +₊ θ ] l

  isPropIsLimit : ∀ x l → isProp (isLimit x l)
  isPropIsLimit x l = isPropΠ2 λ ε δ → isProp≈ (x ε) l (ε +₊ δ)

  limit : (ℚ₊ → M) → Type (ℓ-max ℓ ℓ')
  limit x = Σ[ l ∈ M ] isLimit x l

  isPropLimit : ∀ x → isProp (limit x)
  isPropLimit x (l , l-lim) (l' , l'-lim) = Σ≡Prop (isPropIsLimit x) $
    isSeparated≈ l l' λ ε →
      subst≈ l l' (
        ⟨ ε /4₊ +₊ ε /4₊ +₊ (ε /4₊ +₊ ε /4₊) ⟩₊ ≡⟨ cong (∘diag ℚ._+_) (/4+/4≡/2 ⟨ ε ⟩₊) ⟩
        ⟨ ε /2₊ +₊ ε /2₊ ⟩₊                     ≡⟨ /2+/2≡id ⟨ ε ⟩₊ ⟩
        ⟨ ε ⟩₊                                  ∎)
      (isTriangular≈ l (x (ε /4₊)) l' (ε /4₊ +₊ ε /4₊) (ε /4₊ +₊ ε /4₊)
        (isSym≈ (x (ε /4₊)) l (ε /4₊ +₊ ε /4₊) (
        l-lim (ε /4₊) (ε /4₊)
          :> (x (ε /4₊) ≈[ (ε /4₊) +₊ (ε /4₊) ] l))
        :> (l ≈[ ε /4₊ +₊ ε /4₊ ] x (ε /4₊)))
        (l'-lim (ε /4₊) (ε /4₊)
        :> (x (ε /4₊) ≈[ ε /4₊ +₊ ε /4₊ ] l'))
      :> (l ≈[ (ε /4₊ +₊ ε /4₊) +₊ (ε /4₊ +₊ ε /4₊) ] l'))
      :> (l ≈[ ε ] l')

  isComplete : Type (ℓ-max ℓ ℓ')
  isComplete = ∀ x → isCauchy x → limit x

  isPropIsComplete : isProp isComplete
  isPropIsComplete = isPropΠ λ _ → isProp→ (isPropLimit _)
