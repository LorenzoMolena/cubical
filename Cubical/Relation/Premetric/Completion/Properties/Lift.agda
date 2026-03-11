open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Properties.Lift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base

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
open import Cubical.Relation.Premetric.Completion.Base renaming (ℭ to ⟨ℭ_⟩)
open import Cubical.Relation.Premetric.Completion.Properties.Closeness renaming
  (ℭPremetricSpace to ℭ ; isCompleteℭ to compℭ)

open PremetricTheory using (isLimit ; limit ; isComplete ; isLimit≈< ; isLim≈- ; isLim≈-₂)
open CategoryStructures using (L≡ ; idᴸ ; _∘L_) renaming (
  PremetricSpaceCategoryᴸ to PrSpaces)

open import Cubical.Reflection.RecordEquiv

open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓM ℓM' ℓN ℓN' : Level

  ℚOCR = ℚOrderedCommRing
  ℚCR  = OrderedCommRing→CommRing ℚOCR
  ℚR   = OrderedCommRing→Ring ℚOCR

open OrderedCommRingReasoning ℚOCR
open OrderedCommRingTheory ℚOCR
open RingTheory ℚR
open Units ℚCR
open IsSemigroup (SemigroupStr.isSemigroup (snd +ℚ₊Semigroup)) using () renaming (
  ·Assoc to +₊Assoc)

min₊ : ℚ₊ → ℚ₊ → ℚ₊
fst (min₊ ε δ) with ⟨ ε ⟩₊ ℚ.≟ ⟨ δ ⟩₊
... | ℚ.lt ε<δ = ⟨ ε ⟩₊
... | ℚ.eq ε≡δ = ⟨ ε ⟩₊
... | ℚ.gt ε>δ = ⟨ δ ⟩₊
snd (min₊ ε δ) with ⟨ ε ⟩₊ ℚ.≟ ⟨ δ ⟩₊
... | ℚ.lt ε<δ = snd ε
... | ℚ.eq ε≡δ = snd ε
... | ℚ.gt ε>δ = snd δ

min₊≤L : ∀ ε δ → min₊ ε δ ≤₊ ε
min₊≤L ε δ with ⟨ ε ⟩₊ ℚ.≟ ⟨ δ ⟩₊
... | ℚ.lt ε<δ = ℚ.isRefl≤ ⟨ ε ⟩₊
... | ℚ.eq ε≡δ = ℚ.isRefl≤ ⟨ ε ⟩₊
... | ℚ.gt ε>δ = ℚ.<Weaken≤ ⟨ δ ⟩₊ ⟨ ε ⟩₊ ε>δ

min₊≤R : ∀ ε δ → min₊ ε δ ≤₊ δ
min₊≤R ε δ with ⟨ ε ⟩₊ ℚ.≟ ⟨ δ ⟩₊
... | ℚ.lt ε<δ = ℚ.<Weaken≤ ⟨ ε ⟩₊ ⟨ δ ⟩₊ ε<δ
... | ℚ.eq ε≡δ = ℚ.≡Weaken≤ ⟨ ε ⟩₊ ⟨ δ ⟩₊ ε≡δ
... | ℚ.gt ε>δ = ℚ.isRefl≤ ⟨ δ ⟩₊

min/2₊<L : ∀ ε δ → (min₊ ε δ /2₊) <₊ ε
min/2₊<L ε δ = begin<
  ⟨ min₊ ε δ /2₊ ⟩₊ <⟨ /2₊<id (min₊ ε δ) ⟩
  ⟨ min₊ ε δ ⟩₊     ≤⟨ min₊≤L ε δ ⟩
  ⟨ ε ⟩₊            ◾

min/2₊<R : ∀ ε δ → (min₊ ε δ /2₊) <₊ δ
min/2₊<R ε δ = begin<
  ⟨ min₊ ε δ /2₊ ⟩₊ <⟨ /2₊<id (min₊ ε δ) ⟩
  ⟨ min₊ ε δ ⟩₊     ≤⟨ min₊≤R ε δ ⟩
  ⟨ δ ⟩₊            ◾


module _ (M' : PremetricSpace ℓM ℓM') (N' : PremetricSpace ℓN' ℓN) where

  private
    M = ⟨ M' ⟩
    N = ⟨ N' ⟩
    open module M  = PremetricStr (M' .snd)
    open module CM = PremetricStr ((ℭ M') .snd)
    open module N  = PremetricStr (N' .snd)
    open import Cubical.Relation.Premetric.Completion.Elim M'

  -- Theorem 3.19
  continuous≡ : (f g : C[ ℭ M' , N' ]) → (fst f ∘ ι ≡ fst g ∘ ι) → f ≡ g
  continuous≡ (f , fc) (g , gc) f∘ι≡g∘ι = ΣPathPProp (flip (isPropIsContinuous _) _)
    (funExt (Elimℭ-Prop.go e))
    where
      open Elimℭ-Prop
      open IsContinuousAt

      e : Elimℭ-Prop λ x → f x ≡ g x
      ιA      e          = funExt⁻ f∘ι≡g∘ι
      limA    e x xc IH  = N.isSeparated≈ (f (lim x xc)) (g (lim x xc)) λ ε →
        PT.rec2
          (N.isProp≈ (f (lim x xc)) (g (lim x xc)) ε)
          (λ { (δf , ∼δf→≈ε/2) (δg , ∼δg→≈ε/2) →
            let
              δ    = min₊ δf δg /2₊
              δ<δf = min/2₊<L δf δg
              δ<δg = min/2₊<R δf δg
            in
              N.subst≈ (f (lim x xc)) (g (lim x xc)) (/2+/2≡id ⟨ ε ⟩₊)
              (N.isTriangular≈ (f (lim x xc)) (f (x δ)) (g (lim x xc)) (ε /2₊) (ε /2₊)
                (∼δf→≈ε/2 (x δ) (CM.isSym≈ (x δ) (lim x xc) δf (
                  isLimit≈< (ℭ M') x (lim x xc) (isLimitLim M' x xc) δ δf δ<δf
                      :> x δ CM.≈[ δf ] lim x xc)
                    :> lim x xc CM.≈[ δf ] x δ)
                  :> f (lim x xc) N.≈[ ε /2₊ ] f (x δ))
                (N.isSym≈ (g (lim x xc)) (f (x δ)) (ε /2₊)
                  (subst (N._≈[_]_ _ (ε /2₊)) (sym (IH δ))
                    (∼δg→≈ε/2 (x δ) ((CM.isSym≈ (x δ) (lim x xc) δg
                          (isLimit≈< (ℭ M') x (lim x xc) (isLimitLim M' x xc) δ δg δ<δg
                          :> x δ CM.≈[ δg ] lim x xc))
                        :> lim x xc CM.≈[ δg ] x δ)
                      :> g (lim x xc) N.≈[ ε /2₊ ] g (x δ))
                    :> g (lim x xc) N.≈[ ε /2₊ ] f (x δ))
                  :> f (x δ) N.≈[ ε /2₊ ] g (lim x xc))
                :> f (lim x xc) N.≈[ ε /2₊ +₊ ε /2₊ ] g (lim x xc))
              :> f (lim x xc) N.≈[ ε ] g (lim x xc) })
          (fc (lim x xc) .pres≈ (ε /2₊))
          (gc (lim x xc) .pres≈ (ε /2₊))
      isPropA e x        = N.isSetM (f x) (g x)

  ucontinuous≡ : (f g : UC[ ℭ M' , N' ]) → (fst f ∘ ι ≡ fst g ∘ ι) → f ≡ g
  ucontinuous≡ f g =
    Σ≡Prop (λ _ → squash₁) ∘ cong fst ∘ continuous≡ fC gC
    where
      fC gC : C[ ℭ M' , N' ]
      fC = fst f , isUniformlyContinuous→isContinuous _ (fst f) _ (snd f)
      gC = fst g , isUniformlyContinuous→isContinuous _ (fst g) _ (snd g)

  lipschitz≡ : (f g : L[ ℭ M' , N' ]) → (fst f ∘ ι ≡ fst g ∘ ι) → f ≡ g
  lipschitz≡ f g =
    Σ≡Prop (λ _ → squash₁) ∘ cong fst ∘ continuous≡ fC gC
    where
      fC gC : C[ ℭ M' , N' ]
      fC = fst f , isLipschitz→isContinuous _ (fst f) _ (snd f)
      gC = fst g , isLipschitz→isContinuous _ (fst g) _ (snd g)

  nonExpanding≡ : (f g : NE[ ℭ M' , N' ]) → (fst f ∘ ι ≡ fst g ∘ ι) → f ≡ g
  nonExpanding≡ f g =
    Σ≡Prop (λ _ → isPropIsNonExpanding _ _ _) ∘ cong fst ∘ continuous≡ fC gC
    where
      fC gC : C[ ℭ M' , N' ]
      fC = fst f , isNonExpanding→isContinuous _ (fst f) _ (snd f)
      gC = fst g , isNonExpanding→isContinuous _ (fst g) _ (snd g)

  module _ (N-com : isComplete N') where
    -- Theorem 3.20
    liftLipschitzWith : ∀ L → (f : M → N) → IsLipschitzWith (snd M') f (snd N') L
                      → Σ[ f' ∈ (⟨ℭ M' ⟩ → N) ] IsLipschitzWith (snd (ℭ M')) f' (snd N') L
    liftLipschitzWith L f f-lip =
      RecℭSym.go r , islipschitzwith (λ _ _ _ → RecℭSym.go∼ r) where
      open RecℭSym
      open ℚ₊Inverse
      open IsLipschitzWith

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
      r .ιA        = f
      r .limA      = flim
      r .eqA       = λ u v u≈v →
        N.isSeparated≈ u v (λ ε → N.subst≈ u v (·/ L ε) (u≈v (ε / L)))
      r .ι-ι-B     = f-lip .pres≈
      r .ι-lim-B   x fy ε δ fycL Δ fx≈fyδ        =
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
      r .lim-lim-B fx fy ε δ η fxcL fycL Δ fxδ≈fyη  =
        isLim≈-₂ N' (fx ∘ (_/ L)) (fy ∘ (_/ L)) (flim fx fxcL) (flim fy fycL)
        (L ·₊ ε) (L ·₊ δ) (L ·₊ η) Δ' (islim-flim fx fxcL) (islim-flim fy fycL)
        (subst2 (N._≈[ (L ·₊ ε) -₊ (L ·₊ δ +₊ (L ·₊ η)) , Δ' ]_)
          (cong fx (ℚ₊≡ $ sym (·/ L δ) ∙ ℚ.·Assoc ⟨ L ⟩₊ ⟨ δ ⟩₊ ⟨ L ⁻¹₊ ⟩₊))
          (cong fy (ℚ₊≡ $ sym (·/ L η) ∙ ℚ.·Assoc ⟨ L ⟩₊ ⟨ η ⟩₊ ⟨ L ⁻¹₊ ⟩₊))
          (N.subst≈ (fx δ) (fy η)
            (ℚ.·DistL+ ⟨ L ⟩₊ ⟨ ε ⟩₊ _ ∙ cong (⟨ L ·₊ ε ⟩₊ ℚ.+_)
            (-DistR· ⟨ L ⟩₊ _ ∙ cong ℚ.-_ (ℚ.·DistL+ ⟨ L ⟩₊ ⟨ δ ⟩₊ ⟨ η ⟩₊)))
          fxδ≈fyη :> fx δ N.≈[ (L ·₊ ε) -₊ (L ·₊ δ +₊ (L ·₊ η)) , Δ' ] fy η)
          :> fx ((L ·₊ δ) / L) N.≈[ (L ·₊ ε) -₊ (L ·₊ δ +₊ (L ·₊ η)) , Δ' ] fy ((L ·₊ η) / L))
        :> flim fx fxcL N.≈[ L ·₊ ε ] flim fy fycL
        where
          Δ' : 0 <ℚ (L ·₊ ε) -₊ ((L ·₊ δ) +₊ (L ·₊ η))
          Δ' = <→0<- ⟨ (L ·₊ δ) +₊ (L ·₊ η) ⟩₊ ⟨ L ·₊ ε ⟩₊ (begin<
            ⟨ (L ·₊ δ) +₊ (L ·₊ η) ⟩₊ ≡→≤⟨ sym $ ℚ.·DistL+ ⟨ L ⟩₊ ⟨ δ ⟩₊ ⟨ η ⟩₊ ⟩
            ⟨ L ·₊ (δ +₊ η) ⟩₊          <⟨ ·MonoL< _ _ ⟨ L ⟩₊ (snd L)
                                        (0<-→< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ Δ) ⟩
            ⟨ L ·₊ ε ⟩₊                 ◾)
      r .isSymB    = λ u v → N.isSym≈ u v ∘ (L ·₊_)
      r .isPropB   = λ u v → N.isProp≈ u v ∘ (L ·₊_)

    liftLipschitzWithFun : ∀ L f → IsLipschitzWith (snd M') f (snd N') L → ⟨ℭ M' ⟩ → N
    liftLipschitzWithFun = ((fst ∘_) ∘_) ∘ liftLipschitzWith

    isLipschitzLiftLipschitzWith :
      ∀ L f isLip → isLipschitz (snd (ℭ M')) (liftLipschitzWithFun L f isLip) (snd N')
    isLipschitzLiftLipschitzWith L f isLip = ∣ L , snd (liftLipschitzWith L f isLip) ∣₁

    isIrrelevantLiftLipschitzWith : ∀ L L' f isLip isLip'
      → liftLipschitzWithFun L f isLip ≡ liftLipschitzWithFun L' f isLip'
    isIrrelevantLiftLipschitzWith L L' f isLip isLip' = cong fst $
      lipschitz≡
        (_ , isLipschitzLiftLipschitzWith L  f isLip )
        (_ , isLipschitzLiftLipschitzWith L' f isLip')
        refl

    isUniqueLiftLipschitz : ∀ (f : L[ M' , N' ])
                            → isProp (Σ[ g ∈ L[ ℭ M' , N' ] ] fst g ∘ ι ≡ fst f)
    isUniqueLiftLipschitz = uncurry λ f → PT.rec isPropIsProp λ
      { (L , f-lip) ((g , g-lip) , g∘ι≡f) ((h , h-lip) , h∘ι≡f) →
        Σ≡Prop
        (λ g → λ p q i j x → N.isSetM (fst g (ι x)) (f x) (λ k → p k x) (λ k → q k x) i j)
        (Σ≡Prop (λ _ → squash₁)
          (cong fst (lipschitz≡ (g , g-lip) (h , h-lip) (g∘ι≡f ∙ sym h∘ι≡f)))) }

    liftLipschitzExtension : (f : L[ M' , N' ])
                           → Σ[ g ∈ L[ ℭ M' , N' ] ] (fst g ∘ ι ≡ fst f)
    liftLipschitzExtension = uncurry λ f → PT.elim (curry isUniqueLiftLipschitz f) λ
      { (L , isLip) .fst .fst → liftLipschitzWithFun L f isLip
      ; (L , isLip) .fst .snd → isLipschitzLiftLipschitzWith L f isLip
      ; (L , isLip) .snd      → refl }

    liftLipschitz : L[ M' , N' ] → L[ ℭ M' , N' ]
    liftLipschitz = fst ∘ liftLipschitzExtension

    liftLipschitzFun : L[ M' , N' ] → ⟨ℭ M' ⟩ → N
    liftLipschitzFun = fst ∘ liftLipschitz

    lift∘ι : ∀ (f : L[ M' , N' ]) → liftLipschitzFun f ∘ ι ≡ fst f
    lift∘ι = snd ∘ liftLipschitzExtension

module _ {M' : PremetricSpace ℓM ℓM'} where

  ιⁿ : NE[ M' , ℭ M' ]
  fst ιⁿ = ι
  IsNonExpanding.pres≈ (snd ιⁿ) = ι-ι

  ιᶜ : C[ M' , ℭ M' ]
  fst ιᶜ = ι
  snd ιᶜ = isNonExpanding→isContinuous _ ι _ (snd ιⁿ)

  ιᵘᶜ : UC[ M' , ℭ M' ]
  fst ιᵘᶜ = ι
  snd ιᵘᶜ = isNonExpanding→isUniformlyContinuous _ ι _ (snd ιⁿ)

  ιᴸ : L[ M' , ℭ M' ]
  fst ιᴸ = ι
  snd ιᴸ = isNonExpanding→isLipschitz _ ι _ (snd ιⁿ)

isComplete→≃ℭ : ∀ {ℓ} {M : PremetricSpace ℓ ℓ} → isComplete M → ⟨ M ⟩ ≃ ⟨ℭ M ⟩
isComplete→≃ℭ {M = M} isCompM = isoToEquiv M≅ℭM
  where
  open Iso

  L[id] : L[ ℭ M , M ]
  L[id] = liftLipschitz M M isCompM idᴸ

  M≅ℭM : Iso ⟨ M ⟩ ⟨ℭ M ⟩
  M≅ℭM .fun      = ι
  M≅ℭM .inv      = fst L[id]
  M≅ℭM .rightInv = funExt⁻ $ cong fst $
    lipschitz≡ _ _ (ιᴸ ∘L L[id]) idᴸ (cong ((ι {M' = M}) ∘_) (lift∘ι M M isCompM idᴸ))
  M≅ℭM .leftInv  = funExt⁻ (lift∘ι M M isCompM idᴸ)

-- This theorem needs the relation ≈ and the underlying type ⟨ M ⟩ to live in the same
-- universe to be well-typed if we want to state it without using `Lift`s:
-- Theorem 3.21
isComplete→≡ℭ : ∀ {ℓ} {M : PremetricSpace ℓ ℓ} → isComplete M → ⟨ M ⟩ ≡ ⟨ℭ M ⟩
isComplete→≡ℭ = ua ∘ isComplete→≃ℭ

isIdempotentℭ : ∀ {ℓ} {M : PremetricSpace ℓ ℓ} → ⟨ℭ M ⟩ ≡ ⟨ℭ ℭ M ⟩
isIdempotentℭ = isComplete→≡ℭ (compℭ _)

module CompletionFunctor (ℓ : Level) where

  -- TO DO: prove that the category is univalent, and as a consequence,
  -- conclude the following generalization of Theorem 3.21: "M ≡ ℭ M"
  -- obtaining an equality between the *premetric spaces*, instead of only
  -- between the underlying types (and similarly for isIdempotentℭ)

  open Functor

  ℭFunctor : Functor (PrSpaces ℓ ℓ) (PrSpaces ℓ ℓ)
  F-ob  ℭFunctor = ℭ
  F-hom ℭFunctor = liftLipschitz _ (ℭ _) (compℭ _) ∘ (ιᴸ ∘L_)
  F-id  ℭFunctor = lipschitz≡ _ (ℭ _) _ _ refl
  F-seq ℭFunctor = λ f g →
    let
      ℭ[_] : {M N : PremetricSpace ℓ ℓ} → L[ M , N ] → ⟨ℭ M ⟩ → ⟨ℭ N ⟩
      ℭ[_] = fst ∘ (F-hom ℭFunctor)
    in
      lipschitz≡ _ (ℭ _) _ _ $
      ℭ[ g ∘L f ] ∘ ι     ≡⟨ lift∘ι _ (ℭ _) (compℭ _) (ιᴸ ∘L (g ∘L f)) ⟩
      ι ∘ fst g ∘ fst f   ≡⟨ sym $ cong (_∘ fst f) (lift∘ι _ (ℭ _) (compℭ _) (ιᴸ ∘L g)) ⟩
      ℭ[ g ] ∘ ι ∘ fst f  ≡⟨ sym $ cong (ℭ[ g ] ∘_) (lift∘ι _ (ℭ _) (compℭ _) (ιᴸ ∘L f)) ⟩
      ℭ[ g ] ∘ ℭ[ f ] ∘ ι ∎
