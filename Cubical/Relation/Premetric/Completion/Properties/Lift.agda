open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Properties.Lift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Int.Fast as ℤ hiding (_-_ ; -DistR·)
open import Cubical.Data.Int.Fast.Order as ℤ

open import Cubical.Data.Rationals.Fast.Base as ℚ
import Cubical.Data.Rationals.Fast.Properties as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚ using () renaming (_<_ to _<ℚ_)

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Relation.Binary.Properties

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open Characteristic≠2 ℚOrderedCommRing [ 1 / 2 ] (eq/ _ _ refl)

open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open PremetricTheory using (isLimit ; limit ; isComplete ; isLimit≈< ; isLim≈-)

open import Cubical.Reflection.RecordEquiv

open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓM ℓM' ℓN ℓN' : Level

module _ (M' : PremetricSpace ℓM ℓM') (N' : PremetricSpace ℓN' ℓN) where

  private
    M = ⟨ M' ⟩
    N = ⟨ N' ⟩
    open module M = PremetricStr (M' .snd)
    open module N = PremetricStr (N' .snd)
    ℚOCR = ℚOrderedCommRing
    ℚCR  = OrderedCommRing→CommRing ℚOCR
    ℚR   = OrderedCommRing→Ring ℚOCR
    open OrderedCommRingReasoning ℚOCR
    open OrderedCommRingTheory ℚOCR
    open RingTheory ℚR
    open Units ℚCR
    open IsSemigroup (SemigroupStr.isSemigroup (snd +ℚ₊Semigroup)) using () renaming (
      ·Assoc to +₊Assoc)
    open import Cubical.Relation.Premetric.Completion.Base M' renaming (ℭ to ℭM)
    open import Cubical.Relation.Premetric.Completion.Elim M'
    open import Cubical.Relation.Premetric.Completion.Properties.Closeness M' renaming
      (ℭPremetricSpace to ℭMPrSpace)

  -- Theorem 3.19
  continuous≡ : (f g : C[ ℭMPrSpace , N' ]) → ((fst f) ∘ ι ≡ (fst g) ∘ ι) → f ≡ g
  continuous≡ (f , fc) (g , gc) f∘ι≡g∘ι =
    ΣPathPProp (isPropIsContinuous (snd ℭMPrSpace) (snd N'))
    (funExt (Elimℭ-Prop.go e))
    where
      open Elimℭ-Prop

      e : Elimℭ-Prop λ x → f x ≡ g x
      ιA      e         = funExt⁻ f∘ι≡g∘ι
      limA    e x xc IH = N.isSeparated≈ (f (lim x xc)) (g (lim x xc))
        λ ε → PT.rec2
        (N.isProp≈ (f (lim x xc)) (g (lim x xc)) ε)
        (λ {(δf , ∼δf→≈ε) (δg , ∼δg→≈ε) →
          let
            δ' : Σ[ δ ∈ ℚ₊ ] δ <₊ δf × δ <₊ δg
            δ' = case (⟨ δf ⟩₊ ℚ.≟ ⟨ δg ⟩₊) return (λ _ → Σ[ δ ∈ ℚ₊ ] δ <₊ δf × δ <₊ δg)
              of λ
              { (ℚ.lt δf<δg) →
                  δf /2₊
                , /2₊<id δf
                , (begin<
                  ⟨ δf /2₊ ⟩₊ <⟨ /2₊<id δf ⟩
                  ⟨ δf ⟩₊     <⟨ δf<δg ⟩
                  ⟨ δg ⟩₊     ◾)
              ; (ℚ.eq δf≡δg) →
                  δf /2₊
                , /2₊<id δf
                , subst (⟨ δf /2₊ ⟩₊ <ℚ_) δf≡δg (/2₊<id δf)
              ; (ℚ.gt δg<δf) →
                  δg /2₊
                , (begin<
                  ⟨ δg /2₊ ⟩₊ <⟨ /2₊<id δg ⟩
                  ⟨ δg ⟩₊     <⟨ δg<δf ⟩
                  ⟨ δf ⟩₊     ◾)
                , /2₊<id δg }

            δ , δ<δf , δ<δg = δ'
          in
            N.subst≈ (f (lim x xc)) (g (lim x xc)) (/2+/2≡id ⟨ ε ⟩₊)
            (N.isTriangular≈ (f (lim x xc)) (f (x δ)) (g (lim x xc)) (ε /2₊) (ε /2₊)
              (∼δf→≈ε (x δ) (
                isSym∼ (x δ) (lim x xc) δf (
                  isLimit≈< ℭMPrSpace x (lim x xc) (isLimitLim x xc) δ δf δ<δf
                    :> x δ ∼[ δf ] lim x xc)
                  :> lim x xc ∼[ δf ] x δ)
                :> f (lim x xc) N.≈[ ε /2₊ ] f (x δ))
              (subst (N._≈[ ε /2₊ ] g (lim x xc)) (sym (IH δ))
                (N.isSym≈ (g (lim x xc)) (g (x δ)) (ε /2₊)
                  (∼δg→≈ε (x δ) (isSym∼ (x δ) (lim x xc) δg
                      (isLimit≈< ℭMPrSpace x (lim x xc) (isLimitLim x xc) δ δg δ<δg
                        :> x δ ∼[ δg ] lim x xc)
                      :> lim x xc ∼[ δg ] x δ)
                    :> g (lim x xc) N.≈[ ε /2₊ ] g (x δ))
                  :> g (x δ) N.≈[ ε /2₊ ] g (lim x xc))
                :> f (x δ) N.≈[ ε /2₊ ] g (lim x xc))
              :> f (lim x xc) N.≈[ ε /2₊ +₊ ε /2₊ ] g (lim x xc))
            :> f (lim x xc) N.≈[ ε ] g (lim x xc) })
        (fc (lim x xc) (ε /2₊))
        (gc (lim x xc) (ε /2₊))
      isPropA e x       = N.isSetM (f x) (g x)

{-
  -- Theorem 3.20
  LiftLipschitz : isComplete N'
                → ∀ L → (f : M → N) → isLipschitzWith (snd M') (snd N') f L
                → Σ[ f' ∈ (ℭM → N) ] isLipschitzWith (snd ℭMPrSpace) (snd N') f' L
  LiftLipschitz N-com L f f-lip = RecℭSym.go r , λ _ _ _ → RecℭSym.go∼ r where
    open RecℭSym
    open ℚ₊Inverse

    flim' : ∀ fx → (∀ ε δ → fx ε N.≈[ L ·₊ (ε +₊ δ) ] fx δ) → limit N' (fx ∘ (_/ L))
    flim' fx fxcL = N-com (fx ∘ (_/ L)) fxc where
      fxc : ∀ ε δ → fx (ε / L) N.≈[ ε +₊ δ ] fx (δ / L)
      fxc ε δ = flip (N.subst≈ (fx (ε / L)) (fx (δ / L))) (fxcL (ε / L) (δ / L)) $
        ⟨ L ·₊ (ε / L +₊ δ / L) ⟩₊          ≡⟨ ℚ.·DistL+ ⟨ L ⟩₊ ⟨ ε / L ⟩₊ ⟨ δ / L ⟩₊ ⟩
        ⟨ L ·₊ ε / L ⟩₊ ℚ.+ ⟨ L ·₊ δ / L ⟩₊  ≡⟨ cong₂ ℚ._+_ (·/ L ε) (·/ L δ) ⟩
        ⟨ ε +₊ δ ⟩₊                         ∎

    flim : ∀ fx → (∀ ε δ → fx ε N.≈[ L ·₊ (ε +₊ δ) ] fx δ) → N
    flim fx fxcL = fst (flim' fx fxcL)

    islim-flim : ∀ fx fxcL → isLimit N' (fx ∘ (_/ L)) (flim fx fxcL)
    islim-flim fx fxcL = snd (flim' fx fxcL)

    r : RecℭSym N λ u v ε → u N.≈[ L ·₊ ε ] v
    ιA        r = f
    limA      r = flim
    eqA       r = λ u v u≈v →
      N.isSeparated≈ u v (
        λ ε → N.subst≈ u v (·/ L ε)
          (u≈v (ε / L)
          :> (u N.≈[ L ·₊ (ε / L) ] v))
        :> u N.≈[ ε ] v)
      :> u ≡ v
    ι-ι-B     r = f-lip
    ι-lim-B   r x fy ε δ fycL Δ fx≈fyδ        =
      isLim≈- N' (f x) (fy ∘ (_/ L)) (flim fy fycL) (L ·₊ ε) (L ·₊ δ) Δ'
        (islim-flim fy fycL) (
        subst2 ((f x) N.≈[_]_)
          (ℚ₊≡ $ ℚ.·DistL+ ⟨ L ⟩₊ ⟨ ε ⟩₊ _ ∙ cong (⟨ L ·₊ ε ⟩₊ ℚ.+_) (-DistR· ⟨ L ⟩₊ _))
          (cong fy (ℚ₊≡ $ sym (·/ L δ) ∙ ℚ.·Assoc ⟨ L ⟩₊ ⟨ δ ⟩₊ ⟨ L ⁻¹₊ ⟩₊))
          (fx≈fyδ
            :> f x N.≈[ L ·₊ (ε -₊ δ , Δ) ] fy δ)
          :> f x N.≈[ (L ·₊ ε) -₊ (L ·₊ δ) , Δ' ] fy ((L ·₊ δ) / L))
        :> f x N.≈[ L ·₊ ε ] flim fy fycL
      where
        Δ' : 0 <ℚ (L ·₊ ε) -₊ (L ·₊ δ)
        Δ' = <→0<- ⟨ L ·₊ δ ⟩₊ ⟨ L ·₊ ε ⟩₊
              (·MonoL< ⟨ δ ⟩₊ ⟨ ε ⟩₊ ⟨ L ⟩₊ (snd L)
                (0<-→< ⟨ δ ⟩₊ ⟨ ε ⟩₊ Δ))
    lim-lim-B r fx fy ε δ η fxcL fycL Δ fxδ≈fyη  = {!   !}
    isSymB    r u v = N.isSym≈  u v ∘ (L ·₊_)
    isPropB   r u v = N.isProp≈ u v ∘ (L ·₊_)
-}
