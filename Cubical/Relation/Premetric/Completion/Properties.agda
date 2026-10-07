open import Cubical.Relation.Premetric
open import Cubical.Foundations.Prelude

-- we use this combinations of levels to avoid using `Lift`s when not needed
module Cubical.Relation.Premetric.Completion.Properties {ℓ} ℓ'
  (M : PremetricSpace ℓ (ℓ-max ℓ ℓ')) where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals renaming (ℚCommRing to ℚCR)
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.NatPlusOne.Base as ℕ₊₁
open import Cubical.Data.Fast.Int.Base as ℤ hiding (_-_)
open import Cubical.Data.Rationals.Base  as ℚ hiding (isProp∼)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ using () renaming (_<_ to _<ℚ_)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Binary.Properties
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Tactics.CommRingSolver

open PositiveRationals
open 1/2∈ℚ
open PositiveHalvesℚ

private
  module _ (R : CommRing ℓ-zero) where
    open CommRingStr (snd R) using () renaming (_+_ to _+r_)
    opaque
      lemma : ∀ η/4 δ ε →
        (η/4 +r (η/4 +r η/4)) +r δ +r (η/4 +r ε) ≡
        ε +r ((η/4 +r η/4) +r (η/4 +r η/4) +r δ)
      lemma _ _ _ = solve! R

private
  -- from qlbrpl's PR #1228:

  -- some successive implication syntax
  step→ : ∀ {ℓA ℓB} {A : Type ℓA} (B : Type ℓB) → (A → B) → A → B
  step→ _ f = f

  step→⟨⟩ : ∀ {ℓA} (A : Type ℓA) → A → A
  step→⟨⟩ A a = a

  syntax step→ B f x = x →⟨ f ⟩ B
  syntax step→⟨⟩ A a = a →⟨⟩ A
  infixl 2 step→ step→⟨⟩

  begin→ : ∀ {ℓA} (A : Type ℓA) → A → A
  begin→ = idfun

  syntax begin→ A a = begin→[ a ] A
  infixr 3 begin→

private
  ℓ'' = ℓ-max ℓ ℓ'

open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory    ℚOrderedCommRing
open RingTheory (CommRing→Ring ℚCR)

open PremetricStr (snd M)
open import Cubical.Relation.Premetric.Completion.Base M renaming (ℭ to ℭM)
open import Cubical.Relation.Premetric.Completion.Elim M as E
open E public using (isSym∼)
open import Cubical.Relation.Premetric.Completion.Closeness ℓ' M

open PremetricTheory using (isLimit ; limit ; isComplete ; subst≈L ; subst≈R)

-- Lemma 3.5
isRefl∼ : ∀ x ε → x ∼[ ε ] x
isRefl∼ = Elimℭ-Prop.go e where
  e : Elimℭ-Prop λ x → (ε : ℚ₊) → x ∼[ ε ] x
  Elimℭ-Prop.ιA      e = λ x ε → ι-ι (isRefl≈ x ε)
  Elimℭ-Prop.limA    e = λ x xc IH ε → subst∼ _ _
    (cong (⟨ ε ⟩₊ /2 ℚ.+_) (/4+/4≡/2 ⟨ ε ⟩₊) ∙ /2+/2≡id ⟨ ε ⟩₊)
    (lim-lim _ _ xc xc (IH (ε /4₊) (ε /2₊)))
  Elimℭ-Prop.isPropA e = λ x → isPropΠ λ ε → isProp∼ x ε x

-- Lemma 3.6
isSetℭ : isSet ℭM
isSetℭ = reflPropRelImpliesIdentity→isSet
  (λ x y → ∀ ε → x ∼[ ε ] y) isRefl∼ (λ _ _ → isPropΠ (λ _ → isProp∼ _ _ _)) (eqℭ _ _)

isTriangular∼ : ∀ x y z ε δ → x ∼[ ε ] y → y ∼[ δ ] z → x ∼[ ε +₊ δ ] z
isTriangular∼ x y z ε δ x∼y y∼z =
  (B→∼ (isTriangularBall (snd B⟨ x ,⟩) ε δ y z (∼→B x∼y) y∼z))
  where open IsBall

isRounded∼ : ∀ x y ε → x ∼[ ε ] y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × x ∼[ δ ] y
isRounded∼ x y ε x∼y = PT.map (λ (δ , δ<ε , B[δ]x,y) → (δ , δ<ε , B→∼ B[δ]x,y))
  (isRoundedBall (snd B⟨ x ,⟩) ε y (∼→B x∼y))
  where open IsBall

-- Theorem 3.16
ℭPremetricSpace : PremetricSpace ℓ'' ℓ''
fst ℭPremetricSpace = ℭM
PremetricStr._≈[_]_      (snd ℭPremetricSpace) = _∼[_]_
PremetricStr.isPremetric (snd ℭPremetricSpace) = isPMℭ where
  open IsPremetric

  isPMℭ : IsPremetric _∼[_]_
  isSetM        isPMℭ = isSetℭ
  isProp≈       isPMℭ = flip ∘ isProp∼
  isRefl≈       isPMℭ = isRefl∼
  isSym≈        isPMℭ = isSym∼
  isSeparated≈  isPMℭ = eqℭ
  isTriangular≈ isPMℭ = isTriangular∼
  isRounded≈    isPMℭ = isRounded∼

-- Theorem 3.17
isInjectiveι : ∀ x y → ι x ≡ ι y → x ≡ y
isInjectiveι x y ιx≡ιy = isSeparated≈ x y λ ε →
  ∼→B (subst (ι x ∼[ ε ]_) ιx≡ιy (isRefl∼ (ι x) ε))

isEmbeddingι : isEmbedding ι
isEmbeddingι = injEmbedding isSetℭ (isInjectiveι _ _)

ιⁿ : NE[ M , ℭPremetricSpace ]
fst ιⁿ = ι
IsNonExpansive.pres≈ (snd ιⁿ) _ _ _ = ι-ι

ιᶜ : C[ M , ℭPremetricSpace ]
ιᶜ = NE→C ιⁿ

ιᵘᶜ : UC[ M , ℭPremetricSpace ]
ιᵘᶜ = NE→UC ιⁿ

ιᴸ : L[ M , ℭPremetricSpace ]
ιᴸ = NE→L ιⁿ

open PremetricTheory.PremetricReasoning ℭPremetricSpace

isLimitLim : ∀ x xc → isLimit ℭPremetricSpace x (lim x xc)
isLimitLim = λ x xc ε θ → Elimℭ-Prop.go e (x ε) x xc ε θ (isRefl∼ (x ε) θ) where opaque
  open Elimℭ-Prop
  e : Elimℭ-Prop λ u → ∀ x xc ε θ → u ∼[ θ ] (x ε) → u ∼[ ε +₊ θ ] lim x xc
  ιA      e u x xc ε θ = subst∼ (ι u) (lim x xc) (ℚ.+Comm ⟨ θ ⟩₊ ⟨ ε ⟩₊) ∘ ι-lim ε xc
  limA    e u uc IH x xc ε θ limu∼[θ]xε = proof _ , isProp∼ _ _ _ by do
    (δ , δ<θ , limu∼[δ]xε) ← isRounded∼ (lim u uc) (x ε) θ limu∼[θ]xε
    let
      η = [ θ -₊ δ ]⟨ δ<θ ⟩ ; 3η/4 = η /4₊ +₊ (η /4₊ +₊ η /4₊)
      step =
          lemma ℚCR ⟨ η /4₊ ⟩₊ _ _
        ∙ cong (λ - → ⟨ ε ⟩₊ ℚ.+ (- ℚ.+ _)) (/4+/4+/4+/4≡id ⟨ η ⟩₊)
        ∙ cong (⟨ ε ⟩₊ ℚ.+_) (minusPlus₊ θ δ)
    return ((begin≈[ 3η/4 +₊ δ ]⟨⟩
      u (η /4₊) ≈[ 3η/4  ]⟨ IH (η /4₊) u uc _ _ (uc (η /4₊) (η /4₊)) ⟩
      lim u uc  ≈[   δ   ]⟨ limu∼[δ]xε ⟩
      x ε       ≈∎
      :>
      u (η /4₊) ∼[ 3η/4 +₊ δ ] x ε)                       →⟨ lim-lim (η /4₊) ε uc xc ⟩
      lim u uc  ∼[ (3η/4 +₊ δ) +₊ (η /4₊ +₊ ε) ] lim x xc →⟨ subst∼ _ _ step ⟩
      lim u uc  ∼[ ε +₊ θ ] lim x xc                      )
  isPropA e u = isPropΠ5 λ x xc ε θ _ → isProp∼ u (ε +₊ θ) (lim x xc)

-- Theorem 3.18
isCompleteℭ : isComplete ℭPremetricSpace
isCompleteℭ x xc = lim x xc , isLimitLim x xc
