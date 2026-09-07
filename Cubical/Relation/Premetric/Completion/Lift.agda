{- WIP! -}
module Cubical.Relation.Premetric.Completion.Lift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monad.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Fast.Int as ℤ hiding (_-_ ; -DistR·)
import Cubical.Data.Fast.Int.Order as ℤ

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ using () renaming (_<_ to _<ℚ_)

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Relation.Binary.Properties

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals renaming (ℚCommRing to ℚCR)
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Completion.Base renaming (ℭ to ⟨ℭ_⟩)
open import Cubical.Relation.Premetric.Completion.Properties renaming
  (ℭPremetricSpace to ℭ ; isCompleteℭ to compℭ)
import Cubical.Relation.Premetric.Completion.Properties as ℭProperties

open import Cubical.Reflection.RecordEquiv

open import Cubical.Tactics.CommRingSolver

open RingTheory (CommRing→Ring ℚCR)
open OrderedCommRingStr (str ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

open PremetricTheory using (isLimit ; limit ; isComplete ; isLimit≈< ; isLim≈- ; isLim≈-₂)
open import Cubical.Categories.Instances.PremetricSpaces

private
  variable
    ℓA ℓA' ℓB ℓB' ℓM ℓM' ℓN ℓN' ℓT ℓT' : Level

private
  module _ (R : CommRing ℓ-zero) where
    open CommRingStr (str R) using () renaming (_+_ to _+r_)
    opaque
      lemma : ∀ ε δ η → δ +r (η +r ε) ≡ ε +r (δ +r η)
      lemma _ _ _ = solve! R

module _ (M : PremetricSpace ℓM (ℓ-max ℓM ℓM')) (N : PremetricSpace ℓN' ℓN) where

  private
    ℭM = ℭ ℓM' M
    module PM where
      open PremetricStr (str M) public
      open PremetricTheory M public
      open PremetricReasoning public
    module CM where
      open PremetricStr (str ℭM) public
      open PremetricTheory ℭM public
      open PremetricReasoning public
      open ℭProperties ℓM' M public
    module N where
      open PremetricStr (str N) public
      open PremetricTheory N public
      open PremetricReasoning public
    open import Cubical.Relation.Premetric.Completion.Elim M

  -- Theorem 3.19
  continuous≡ : (f g : C[ ℭM , N ])
              → (∀ z → fst f (ι z) ≡ fst g (ι z)) → ∀ z → fst f z ≡ fst g z
  continuous≡ (f , fc) (g , gc) f∘ι≡g∘ι = Elimℭ-Prop.go e where
    open Elimℭ-Prop
    open IsContinuousAt

    e : Elimℭ-Prop λ x → f x ≡ g x
    ιA      e = f∘ι≡g∘ι
    limA    e x xc IH = N.isSeparated≈ _ _ λ ε → proof _ , N.isProp≈ _ _ ε by do
      (δf , ∼δf→≈ε/2) ← fc (lim x xc) .pres≈ (ε /2₊)
      (δg , ∼δg→≈ε/2) ← gc (lim x xc) .pres≈ (ε /2₊)
      let
        δ = (min₊ δf δg) /2₊

        limx≈[δf]xδ : lim x xc CM.≈[ δf ] x δ
        limx≈[δf]xδ = CM.isSym≈ _ _ _
          (CM.isLimit≈< x _ (CM.isLimitLim x xc) _ _ (min/2₊<L δf δg))

        limx≈[δg]xδ : lim x xc CM.≈[ δg ] x δ
        limx≈[δg]xδ = CM.isSym≈ _ _ _
          (CM.isLimit≈< x _ (CM.isLimitLim x xc) _ _ (min/2₊<R δf δg))

      return (N.begin≈[ ε ]⟨ /2+/2≡id ⟨ ε ⟩₊ ⟩
        f (lim x xc)             N.≈[ ε /2₊ ]⟨ ∼δf→≈ε/2 _ limx≈[δf]xδ ⟩
        f (x ((min₊ δf δg) /2₊)) N.≡→≈⟨ IH ((min₊ δf δg) /2₊) ⟩
        g (x ((min₊ δf δg) /2₊)) N.≈[ ε /2₊ ]⟨ N.≈⁻ ∼δg→≈ε/2 _ limx≈[δg]xδ ⟩
        g (lim x xc)             N.≈∎)
    isPropA e x = N.isSetM (f x) (g x)

  uContinuous≡ : (f g : UC[ ℭM , N ])
               → (∀ z → fst f (ι z) ≡ fst g (ι z)) → ∀ z → fst f z ≡ fst g z
  uContinuous≡ f g = continuous≡ (UC→C f) (UC→C g)

  lipschitz≡ : (f g : L[ ℭM , N ])
             → (∀ z → fst f (ι z) ≡ fst g (ι z)) → ∀ z → fst f z ≡ fst g z
  lipschitz≡ f g = continuous≡ (L→C f) (L→C g)

  nonExpansive≡ : (f g : NE[ ℭM , N ])
                → (∀ z → fst f (ι z) ≡ fst g (ι z)) → ∀ z → fst f z ≡ fst g z
  nonExpansive≡ f g = continuous≡ (NE→C f) (NE→C g)

  module LiftCompleteCodomain (N-com : isComplete N) where

    private
      limN : ∀ x → N.isCauchy x → ⟨ N ⟩
      limN = (fst ∘_) ∘ N-com

      isLimitN : ∀ x xc → N.isLimit x (limN x xc)
      isLimitN = (snd ∘_) ∘ N-com

    liftNonExpansive liftNE : NE[ M , N ] → NE[ ℭM , N ]
    liftNonExpansive (f , is-ne) = RecℭSym.go r , isnonexpansive λ _ _ _ → RecℭSym.go∼ r
      module liftNonExpansive where
      open RecℭSym
      open IsNonExpansive

      r : RecℭSym ⟨ N ⟩ λ u v ε → u N.≈[ ε ] v
      r .ιA        = f
      r .limA      = λ f∘x f∘xc → fst (N-com f∘x f∘xc)
      r .eqA       = N.isSeparated≈
      r .ι-ι-B     = IsNonExpansive.pres≈ is-ne
      r .ι-lim-B   = λ x y ε δ yc → N.subst≈ _ _ (ℚ.+Comm ⟨ δ ⟩₊ ⟨ ε ⟩₊) ∘
        N.isLim≈+ (f x) y (fst (N-com y yc)) δ ε (snd (N-com y yc))
      r .lim-lim-B = λ x y ε δ η xc yc → N.subst≈ _ _ (lemma ℚCR ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟨ η ⟩₊) ∘
        N.isLim≈+₂ x y _ _ ε δ η (snd (N-com x xc)) (snd (N-com y yc))
      r .isSymB    = N.isSym≈
      r .isPropB   = N.isProp≈

    liftNE = liftNonExpansive

    liftNE∘ι : (f : NE[ M , N ]) → fst (liftNE f) ∘ ι ≡ fst f
    liftNE∘ι f = refl

    isCauchyliftNE : ∀ f x → CM.isCauchy x → N.isCauchy (fst (liftNE f) ∘ x)
    isCauchyliftNE f x xc ε δ = IsNonExpansive.pres≈ (snd (liftNE f)) _ _ _ (xc ε δ)

    liftNE∘lim : ∀ f x xc
      → fst (liftNE f) (lim x xc) ≡ limN (fst (liftNE f) ∘ x) (isCauchyliftNE f x xc)
    liftNE∘lim f x xc = refl

    -- Lemma 3.24
    ≈→liftNE≈ : (f g : NE[ M , N ]) → ∀ ε
              → (∀ x δ → fst f x N.≈[ ε +₊ δ ] fst g x)
              →  ∀ x δ → fst (liftNE f) x N.≈[ ε +₊ δ ] fst (liftNE g) x
    ≈→liftNE≈ f g ε f≈g = Elimℭ-Prop.go r module ≈→liftNE≈ where
      open Elimℭ-Prop
      r : Elimℭ-Prop λ x → ∀ δ → fst (liftNE f) x N.≈[ ε +₊ δ ] fst (liftNE g) x
      r .ιA = f≈g
      r .limA x xc IH δ = N.subst≈
        (limN (fst (liftNE f) ∘ x) (isCauchyliftNE f x xc))
        (limN (fst (liftNE g) ∘ x) (isCauchyliftNE g x xc))
        δ/4+δ/4+ε+δ/2≡ε+δ
        (N.isLim≈+₂
          (fst (liftNE f) ∘ x) (fst (liftNE g) ∘ x) _ _ (ε +₊ δ /2₊) (δ /4₊) (δ /4₊)
          (isLimitN _ (isCauchyliftNE f x xc)) (isLimitN _ (isCauchyliftNE g x xc))
          (IH (δ /4₊) (δ /2₊)))
        where
        δ/4+δ/4+ε+δ/2≡ε+δ : ⟨ (δ /4₊) +₊ ((δ /4₊) +₊ (ε +₊ (δ /2₊))) ⟩₊ ≡ ⟨ ε +₊ δ ⟩₊
        δ/4+δ/4+ε+δ/2≡ε+δ =
          ⟨ δ /4₊ +₊ (δ /4₊ +₊ (ε +₊ δ /2₊)) ⟩₊ ≡⟨ ℚ.+Assoc ⟨ δ /4₊ ⟩₊ _ _ ⟩
          ⟨ (δ /4₊ +₊ δ /4₊) +₊ (ε +₊ δ /2₊) ⟩₊ ≡⟨ cong (ℚ._+ ⟨ ε +₊ δ /2₊ ⟩₊) (/4+/4≡/2 ⟨ δ ⟩₊) ⟩
          ⟨ δ /2₊ +₊ (ε +₊ δ /2₊) ⟩₊            ≡⟨ ℚ.+Comm ⟨ δ /2₊ ⟩₊ _ ⟩
          ⟨ (ε +₊ δ /2₊) +₊ δ /2₊ ⟩₊            ≡⟨ sym $ ℚ.+Assoc ⟨ ε ⟩₊ ⟨ δ /2₊ ⟩₊ _ ⟩
          ⟨ ε +₊ (δ /2₊ +₊ δ /2₊) ⟩₊            ≡⟨ cong (⟨ ε ⟩₊ ℚ.+_) (/2+/2≡id ⟨ δ ⟩₊) ⟩
          ⟨ ε +₊ δ ⟩₊                           ∎
      r .isPropA = λ _ → isPropΠ λ _ → N.isProp≈ _ _ _

    liftNEⁿ : NE[ NE[ M , N ]PrSpace , NE[ ℭM , N ]PrSpace ]
    fst liftNEⁿ = liftNE
    IsNonExpansive.pres≈ (snd liftNEⁿ) fⁿ@(f , f-ne) gⁿ@(g , g-ne) ε = PT.map proof where
      proof : Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × (∀ x → f x N.≈[ δ ] g x)
            → Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × (∀ x → fst (liftNE fⁿ) x N.≈[ δ ] fst (liftNE gⁿ) x)
      proof (δ , δ<ε , ptwf≈g) .fst      = mean₊ δ ε
      proof (δ , δ<ε , ptwf≈g) .snd .fst = <→mean< ⟨ δ ⟩₊ ⟨ ε ⟩₊ δ<ε
      proof (δ , δ<ε , ptwf≈g) .snd .snd = λ x → N.subst≈ _ _
        (ℚ.+Comm ⟨ δ ⟩₊ (⟨ mean₊ δ ε ⟩₊ ℚ.- ⟨ δ ⟩₊) ∙ minusPlus₊ (mean₊ δ ε) δ) $
        ≈→liftNE≈ fⁿ gⁿ δ
          (λ x η → N.isMonotone≈< {ε = δ} {δ +₊ η} (<₊SumLeft δ η) (ptwf≈g x))
          x [ mean₊ δ ε -₊ δ ]⟨ <→<mean ⟨ δ ⟩₊ ⟨ ε ⟩₊ δ<ε ⟩

module _ {ℓA ℓA' ℓB ℓB'}
  (A : PremetricSpace ℓA (ℓ-max ℓA ℓA'))
  (B : PremetricSpace ℓB (ℓ-max ℓB ℓB'))
  (N : PremetricSpace ℓN' ℓN) where

  private
    ℭA = ℭ ℓA' A
    ℭB = ℭ ℓB' B

  nonExpansive₂≡ : (f g : NE[ ℭA , NE[ ℭB , N ]PrSpace ])
                 → (∀ x y → fst (fst f (ι x)) (ι y) ≡ fst (fst g (ι x)) (ι y))
                 → ∀ x y → fst (fst f x) y ≡ fst (fst g x) y
  nonExpansive₂≡ f g fιι≡gιι =
    funExt⁻ ∘ (cong fst) ∘ nonExpansive≡ A NE[ ℭB , N ]PrSpace f g
    (NE≡ ∘ funExt ∘ λ x → nonExpansive≡ B N (fst f (ι x)) (fst g (ι x)) (fιι≡gιι x))

  module LiftCompleteCodomain₂ (N-com : isComplete N) where

    open LiftCompleteCodomain {ℓM' = ℓB'} B N N-com using (liftNEⁿ)
    open LiftCompleteCodomain {ℓM' = ℓA'} A NE[ ℭB , N ]PrSpace (isCompleteNE ℭB N N-com)
      using (liftNonExpansive)

    liftNonExpansive₂ liftNE₂ : NE[ A , NE[ B , N ]PrSpace ] → NE[ ℭA , NE[ ℭB , N ]PrSpace ]
    liftNonExpansive₂ = liftNonExpansive ∘ liftNEⁿ ∘NE_

    liftNE₂ = liftNonExpansive₂

    liftNE₂∘ι : ∀ f x y → fst (fst (liftNE₂ f) (ι x)) (ι y) ≡ fst (fst f x) y
    liftNE₂∘ι f x y = refl
