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
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monad.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Int.Fast as ℤ hiding (_-_ ; -DistR·)
import Cubical.Data.Int.Fast.Order as ℤ

open import Cubical.Data.Rationals.Fast.Base as ℚ
import Cubical.Data.Rationals.Fast.Properties as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚ using () renaming (_<_ to _<ℚ_)

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Relation.Binary.Properties

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals.Fast
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Completion.Base renaming (ℭ to ⟨ℭ_⟩)
open import Cubical.Relation.Premetric.Completion.Properties.Closeness renaming
  (ℭPremetricSpace to ℭ)
  -- ; isCompleteℭ to compℭ)

open import Cubical.Reflection.RecordEquiv

open import Cubical.Tactics.CommRingSolver

open RingTheory (CommRing→Ring ℚCommRing)
open OrderedCommRingStr (str ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

open PremetricTheory using (isLimit ; limit ; isComplete ; isLimit≈< ; isLim≈- ; isLim≈-₂)
open CategoryStructures using (NE≡ ; idⁿ ; _∘NE_ ; L≡ ; idᴸ ; _∘L_)
  renaming (PremetricSpaceCategoryⁿ to PrSpacesⁿ ; PremetricSpaceCategoryᴸ to PrSpacesᴸ)

private
  RCR = ℚCommRing
  variable
    ℓA ℓA' ℓB ℓB' ℓM ℓM' ℓN ℓN' ℓT ℓT' : Level

module _ (M' : PremetricSpace ℓM ℓM') (N' : PremetricSpace ℓN' ℓN) where

  private
    M = ⟨ M' ⟩
    N = ⟨ N' ⟩
    open module PM  = PremetricStr (M' .snd)
    open module PCM = PremetricStr ((ℭ M') .snd)
    open module PN  = PremetricStr (N' .snd)
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
      limA    e x xc IH  = PN.isSeparated≈ (f (lim x xc)) (g (lim x xc)) λ ε →
        PT.rec2
          (PN.isProp≈ (f (lim x xc)) (g (lim x xc)) ε)
          (λ { (δf , ∼δf→≈ε/2) (δg , ∼δg→≈ε/2) →
            let
              δ    = min₊ δf δg /2₊
              δ<δf = min/2₊<L δf δg
              δ<δg = min/2₊<R δf δg
            in
              PN.subst≈ (f (lim x xc)) (g (lim x xc)) (/2+/2≡id ⟨ ε ⟩₊)
              (PN.isTriangular≈ (f (lim x xc)) (f (x δ)) (g (lim x xc)) (ε /2₊) (ε /2₊)
                (∼δf→≈ε/2 (x δ) (PCM.isSym≈ (x δ) (lim x xc) δf (
                  isLimit≈< (ℭ M') x (lim x xc) (isLimitLim M' x xc) δ δf δ<δf
                      :> x δ PCM.≈[ δf ] lim x xc)
                    :> lim x xc PCM.≈[ δf ] x δ)
                  :> f (lim x xc) PN.≈[ ε /2₊ ] f (x δ))
                (PN.isSym≈ (g (lim x xc)) (f (x δ)) (ε /2₊)
                  (subst (PN._≈[_]_ _ (ε /2₊)) (sym (IH δ))
                    (∼δg→≈ε/2 (x δ) ((PCM.isSym≈ (x δ) (lim x xc) δg
                          (isLimit≈< (ℭ M') x (lim x xc) (isLimitLim M' x xc) δ δg δ<δg
                          :> x δ PCM.≈[ δg ] lim x xc))
                        :> lim x xc PCM.≈[ δg ] x δ)
                      :> g (lim x xc) PN.≈[ ε /2₊ ] g (x δ))
                    :> g (lim x xc) PN.≈[ ε /2₊ ] f (x δ))
                  :> f (x δ) PN.≈[ ε /2₊ ] g (lim x xc))
                :> f (lim x xc) PN.≈[ ε /2₊ +₊ ε /2₊ ] g (lim x xc))
              :> f (lim x xc) PN.≈[ ε ] g (lim x xc) })
          (fc (lim x xc) .pres≈ (ε /2₊))
          (gc (lim x xc) .pres≈ (ε /2₊))
      isPropA e x        = PN.isSetM (f x) (g x)

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

  module LiftLipschitzCompleteCodomain (N-com : isComplete N') where
    -- Theorem 3.20
    liftLipschitzWith : ∀ L → (f : M → N) → IsLipschitzWith (snd M') f (snd N') L
                      → Σ[ f' ∈ (⟨ℭ M' ⟩ → N) ] IsLipschitzWith (snd (ℭ M')) f' (snd N') L
    liftLipschitzWith L f f-lip =
      RecℭSym.go r , islipschitzwith (λ _ _ _ → RecℭSym.go∼ r) where
      open RecℭSym
      open ℚ₊Inverse
      open IsLipschitzWith

      flim' : ∀ fx → (∀ ε δ → fx ε PN.≈[ L ·₊ (ε +₊ δ) ] fx δ) → limit N' (fx ∘ (_/ L))
      flim' fx fxcL = N-com (fx ∘ (_/ L)) fxc where
        fxc : ∀ ε δ → fx (ε / L) PN.≈[ ε +₊ δ ] fx (δ / L)
        fxc ε δ = flip (PN.subst≈ (fx (ε / L)) (fx (δ / L))) (fxcL (ε / L) (δ / L)) $
          ⟨ L ·₊ (ε / L +₊ δ / L) ⟩₊          ≡⟨ ℚ.·DistL+ ⟨ L ⟩₊ ⟨ ε / L ⟩₊ ⟨ δ / L ⟩₊ ⟩
          ⟨ L ·₊ ε / L ⟩₊ ℚ.+ ⟨ L ·₊ δ / L ⟩₊  ≡⟨ cong₂ ℚ._+_ (·/ L ε) (·/ L δ) ⟩
          ⟨ ε +₊ δ ⟩₊                         ∎

      flim : ∀ fx → (∀ ε δ → fx ε PN.≈[ L ·₊ (ε +₊ δ) ] fx δ) → N
      flim fx fxcL = fst (flim' fx fxcL)

      islim-flim : ∀ fx fxcL → isLimit N' (fx ∘ (_/ L)) (flim fx fxcL)
      islim-flim fx fxcL = snd (flim' fx fxcL)

      r : RecℭSym N λ u v ε → u PN.≈[ L ·₊ ε ] v
      r .ιA        = f
      r .limA      = flim
      r .eqA       = λ u v u≈v →
        PN.isSeparated≈ u v (λ ε → PN.subst≈ u v (·/ L ε) (u≈v (ε / L)))
      r .ι-ι-B     = f-lip .pres≈
      r .ι-lim-B   x fy ε δ fycL Δ fx≈fyδ        =
        isLim≈- N' (f x) (fy ∘ (_/ L)) (flim fy fycL) (L ·₊ ε) (L ·₊ δ) Δ'
          (islim-flim fy fycL) (
          subst2 ((f x) PN.≈[_]_)
            (ℚ₊≡ $ ℚ.·DistL+ ⟨ L ⟩₊ ⟨ ε ⟩₊ _ ∙ cong (⟨ L ·₊ ε ⟩₊ ℚ.+_) (-DistR· ⟨ L ⟩₊ _))
            (cong fy (ℚ₊≡ $ sym (·/ L δ) ∙ ℚ.·Assoc ⟨ L ⟩₊ ⟨ δ ⟩₊ ⟨ L ⁻¹₊ ⟩₊))
            (fx≈fyδ
              :> f x PN.≈[ L ·₊ (ε -₊ δ , Δ) ] fy δ)
            :> f x PN.≈[ (L ·₊ ε) -₊ (L ·₊ δ) , Δ' ] fy ((L ·₊ δ) / L))
          :> f x PN.≈[ L ·₊ ε ] flim fy fycL
        where
          Δ' : 0 <ℚ (L ·₊ ε) -₊ (L ·₊ δ)
          Δ' = <→0<Δ ⟨ L ·₊ δ ⟩₊ ⟨ L ·₊ ε ⟩₊
                (·MonoL< ⟨ δ ⟩₊ ⟨ ε ⟩₊ ⟨ L ⟩₊ (snd L)
                  (0<Δ→< ⟨ δ ⟩₊ ⟨ ε ⟩₊ Δ))
      r .lim-lim-B fx fy ε δ η fxcL fycL Δ fxδ≈fyη  =
        isLim≈-₂ N' (fx ∘ (_/ L)) (fy ∘ (_/ L)) (flim fx fxcL) (flim fy fycL)
        (L ·₊ ε) (L ·₊ δ) (L ·₊ η) Δ' (islim-flim fx fxcL) (islim-flim fy fycL)
        (subst2 (PN._≈[ (L ·₊ ε) -₊ (L ·₊ δ +₊ (L ·₊ η)) , Δ' ]_)
          (cong fx (ℚ₊≡ $ sym (·/ L δ) ∙ ℚ.·Assoc ⟨ L ⟩₊ ⟨ δ ⟩₊ ⟨ L ⁻¹₊ ⟩₊))
          (cong fy (ℚ₊≡ $ sym (·/ L η) ∙ ℚ.·Assoc ⟨ L ⟩₊ ⟨ η ⟩₊ ⟨ L ⁻¹₊ ⟩₊))
          (PN.subst≈ (fx δ) (fy η)
            (ℚ.·DistL+ ⟨ L ⟩₊ ⟨ ε ⟩₊ _ ∙ cong (⟨ L ·₊ ε ⟩₊ ℚ.+_)
            (-DistR· ⟨ L ⟩₊ _ ∙ cong ℚ.-_ (ℚ.·DistL+ ⟨ L ⟩₊ ⟨ δ ⟩₊ ⟨ η ⟩₊)))
          fxδ≈fyη :> fx δ PN.≈[ (L ·₊ ε) -₊ (L ·₊ δ +₊ (L ·₊ η)) , Δ' ] fy η)
          :> fx ((L ·₊ δ) / L) PN.≈[ (L ·₊ ε) -₊ (L ·₊ δ +₊ (L ·₊ η)) , Δ' ] fy ((L ·₊ η) / L))
        :> flim fx fxcL PN.≈[ L ·₊ ε ] flim fy fycL
        where
          Δ' : 0 <ℚ (L ·₊ ε) -₊ ((L ·₊ δ) +₊ (L ·₊ η))
          Δ' = <→0<Δ ⟨ (L ·₊ δ) +₊ (L ·₊ η) ⟩₊ ⟨ L ·₊ ε ⟩₊ (begin<
            ⟨ (L ·₊ δ) +₊ (L ·₊ η) ⟩₊ ≡→≤⟨ sym $ ℚ.·DistL+ ⟨ L ⟩₊ ⟨ δ ⟩₊ ⟨ η ⟩₊ ⟩
            ⟨ L ·₊ (δ +₊ η) ⟩₊          <⟨ ·MonoL< _ _ ⟨ L ⟩₊ (snd L)
                                        (0<Δ→< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ Δ) ⟩
            ⟨ L ·₊ ε ⟩₊                 ◾)
      r .isSymB    = λ u v → PN.isSym≈ u v ∘ (L ·₊_)
      r .isPropB   = λ u v → PN.isProp≈ u v ∘ (L ·₊_)

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
        (λ g → λ p q i j x → PN.isSetM (fst g (ι x)) (f x) (λ k → p k x) (λ k → q k x) i j)
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

module _ (A' : PremetricSpace ℓA ℓA') (B' : PremetricSpace ℓB ℓB') (T' : PremetricSpace ℓT ℓT') where

  private
    A = ⟨ A' ⟩
    B = ⟨ B' ⟩
    T = ⟨ T' ⟩
    open module PA  = PremetricStr (A' .snd)
    open module PℭA = PremetricStr ((ℭ A') .snd)
    open module PB  = PremetricStr (B' .snd)
    open module PℭB = PremetricStr ((ℭ B') .snd)
    open module PC  = PremetricStr (T' .snd)

  module _ (T-complete : isComplete T') where
    open ℚ₊Inverse

    private
      F' = →PremetricSpace ⟨ ℭ B' ⟩ T'

      module PF  = PremetricStr (F' .snd)
      module TTh = PremetricTheory T'
      module FTheory = PremetricTheory F'
      module LiftB = LiftLipschitzCompleteCodomain B' T' T-complete

      F-complete : isComplete F'
      F-complete = isComplete→ ⟨ ℭ B' ⟩ T' T-complete

      module LiftA = LiftLipschitzCompleteCodomain A' F' F-complete

    liftCloseness :
      ∀ (L : ℚ₊) (f g : B → T)
      (f-lip : IsLipschitzWith (snd B') f (snd T') L)
      (g-lip : IsLipschitzWith (snd B') g (snd T') L)
      (ε : ℚ₊)
      → (∀ (u : B) (δ : ℚ₊) → f u PC.≈[ ε +₊ δ ] g u)
      → ∀ (u : ⟨ ℭ B' ⟩) (δ : ℚ₊)
      → LiftB.liftLipschitzWithFun L f f-lip u PC.≈[ ε +₊ δ ] LiftB.liftLipschitzWithFun L g g-lip u
    liftCloseness L f g f-lip g-lip ε fg-close = Elimℭ-Prop.go e
      where
      open import Cubical.Relation.Premetric.Completion.Elim B'

      f̄ : ⟨ ℭ B' ⟩ → T
      f̄ = LiftB.liftLipschitzWithFun L f f-lip

      ḡ : ⟨ ℭ B' ⟩ → T
      ḡ = LiftB.liftLipschitzWithFun L g g-lip

      f̄-lip : IsLipschitzWith (snd (ℭ B')) f̄ (snd T') L
      f̄-lip = snd (LiftB.liftLipschitzWith L f f-lip)

      ḡ-lip : IsLipschitzWith (snd (ℭ B')) ḡ (snd T') L
      ḡ-lip = snd (LiftB.liftLipschitzWith L g g-lip)

      isLimit-f̄ : ∀ x xc → isLimit T' ((f̄ ∘ x) ∘ (_/ L)) (f̄ (lim x xc))
      isLimit-f̄ x xc ε' δ =
        PC.subst≈ (f̄ (x (ε' / L))) (f̄ (lim x xc))
          (ℚ.·DistL+ ⟨ L ⟩₊ ⟨ ε' / L ⟩₊ ⟨ δ / L ⟩₊
          ∙ cong₂ ℚ._+_ (·/ L ε') (·/ L δ))
          (IsLipschitzWith.pres≈ f̄-lip
            (x (ε' / L)) (lim x xc) (ε' / L +₊ δ / L)
            (isLimitLim B' x xc (ε' / L) (δ / L)))

      isLimit-ḡ : ∀ x xc → isLimit T' ((ḡ ∘ x) ∘ (_/ L)) (ḡ (lim x xc))
      isLimit-ḡ x xc ε' δ =
        PC.subst≈ (ḡ (x (ε' / L))) (ḡ (lim x xc))
          (ℚ.·DistL+ ⟨ L ⟩₊ ⟨ ε' / L ⟩₊ ⟨ δ / L ⟩₊
          ∙ cong₂ ℚ._+_ (·/ L ε') (·/ L δ))
          (IsLipschitzWith.pres≈ ḡ-lip
            (x (ε' / L)) (lim x xc) (ε' / L +₊ δ / L)
            (isLimitLim B' x xc (ε' / L) (δ / L)))

      e : Elimℭ-Prop (λ u → ∀ δ → f̄ u PC.≈[ ε +₊ δ ] ḡ u)
      e .Elimℭ-Prop.ιA x δ = fg-close x δ
      e .Elimℭ-Prop.limA x xc IH δ =
        PC.isRounded≈⁻ (f̄ (lim x xc)) (ḡ (lim x xc)) (ε +₊ δ)
          ∣ (η +₊ (η +₊ (ε +₊ η))
          , witness<
          , TTh.isLim≈+₂
              (((f̄ ∘ x) ∘ (_/ L)))
              (((ḡ ∘ x) ∘ (_/ L)))
              (f̄ (lim x xc))
              (ḡ (lim x xc))
              (ε +₊ η) η η
              (isLimit-f̄ x xc)
              (isLimit-ḡ x xc)
              (IH (η / L) η))
          ∣₁
        where
        η : ℚ₊
        η = δ /4₊

        tail<δ : ((η +₊ η) +₊ η) <₊ δ
        tail<δ = begin<
          ⟨ (η +₊ η) +₊ η ⟩₊              ≡→≤⟨ cong (ℚ._+ ⟨ η ⟩₊) (/4+/4≡/2 ⟨ δ ⟩₊) ⟩
          ⟨ δ /2₊ +₊ η ⟩₊                 <⟨ +MonoL< ⟨ η ⟩₊ ⟨ δ /2₊ ⟩₊ ⟨ δ /2₊ ⟩₊ (/4₊</2₊ δ) ⟩
          ⟨ δ /2₊ +₊ δ /2₊ ⟩₊            ≡→≤⟨ /2+/2≡id ⟨ δ ⟩₊ ⟩
          ⟨ δ ⟩₊                          ◾

        witness< : η +₊ (η +₊ (ε +₊ η)) <₊ ε +₊ δ
        witness< = begin<
          ⟨ η +₊ (η +₊ (ε +₊ η)) ⟩₊      ≡→≤⟨
            ℚ.+Assoc ⟨ η ⟩₊ ⟨ η ⟩₊ (⟨ ε ⟩₊ ℚ.+ ⟨ η ⟩₊)
            ∙ ℚ.+Assoc (⟨ η ⟩₊ ℚ.+ ⟨ η ⟩₊) ⟨ ε ⟩₊ ⟨ η ⟩₊
            ∙ cong (ℚ._+ ⟨ η ⟩₊) (ℚ.+Comm (⟨ η ⟩₊ ℚ.+ ⟨ η ⟩₊) ⟨ ε ⟩₊)
            ∙ sym (ℚ.+Assoc ⟨ ε ⟩₊ (⟨ η ⟩₊ ℚ.+ ⟨ η ⟩₊) ⟨ η ⟩₊) ⟩
          ⟨ ε +₊ ((η +₊ η) +₊ η) ⟩₊      <⟨ +MonoL< _ _ ⟨ ε ⟩₊ tail<δ ⟩
          ⟨ ε +₊ δ ⟩₊                    ◾
      e .Elimℭ-Prop.isPropA u = isPropΠ λ δ → PC.isProp≈ (f̄ u) (ḡ u) (ε +₊ δ)

    liftLipschitzBinaryWith :
      ∀ (L₁ L₂ : ℚ₊) (f : A → B → T)
      (f-lipA : ∀ y → IsLipschitzWith (snd A') (λ x → f x y) (snd T') L₁)
      (f-lipB : ∀ x → IsLipschitzWith (snd B') (f x) (snd T') L₂)
      → Σ[ f̄ ∈ (⟨ ℭ A' ⟩ → ⟨ ℭ B' ⟩ → T) ]
          ((∀ u → IsLipschitzWith (snd (ℭ B')) (f̄ u) (snd T') L₂)
          × IsLipschitzWith (snd (ℭ A')) f̄ (snd (→PremetricSpace ⟨ ℭ B' ⟩ T')) L₁)
    liftLipschitzBinaryWith L₁ L₂ f f-lipA f-lipB = f̄ , (f̄-lipB , f̄-lipA)
      where
      f₁ : A → ⟨ ℭ B' ⟩ → T
      f₁ x = LiftB.liftLipschitzWithFun L₂ (f x) (f-lipB x)

      f₁-lipB : ∀ x → IsLipschitzWith (snd (ℭ B')) (f₁ x) (snd T') L₂
      f₁-lipB x = snd (LiftB.liftLipschitzWith L₂ (f x) (f-lipB x))

      f₁-lipA : IsLipschitzWith (snd A') f₁ (snd F') L₁
      f₁-lipA .IsLipschitzWith.pres≈ x y ε x≈y =
        PT.rec squash₁ (λ where
          (κ , κ<ε , x≈κy) →
            let
              L₁κ<L₁ε : (L₁ ·₊ κ) <₊ (L₁ ·₊ ε)
              L₁κ<L₁ε = ·MonoL< ⟨ κ ⟩₊ ⟨ ε ⟩₊ ⟨ L₁ ⟩₊ (snd L₁) κ<ε

              gap : ℚ₊
              gap = [ (L₁ ·₊ ε) -₊ (L₁ ·₊ κ) ]⟨ L₁κ<L₁ε ⟩

              δ₀ : ℚ₊
              δ₀ = gap /2₊

              witness< : (L₁ ·₊ κ) +₊ δ₀ <₊ L₁ ·₊ ε
              witness< = subst2 (λ u v → u <ℚ v)
                (ℚ.+Comm ⟨ δ₀ ⟩₊ ⟨ L₁ ·₊ κ ⟩₊)
                (minusPlus₊ (L₁ ·₊ ε) (L₁ ·₊ κ))
                (+MonoR< ⟨ δ₀ ⟩₊ ⟨ gap ⟩₊ ⟨ L₁ ·₊ κ ⟩₊ (/2₊<id gap))

              base-close : ∀ z ρ → f x z PC.≈[ (L₁ ·₊ κ) +₊ ρ ] f y z
              base-close z ρ =
                PC.isMonotone≈< (f x z) (f y z) (L₁ ·₊ κ) ((L₁ ·₊ κ) +₊ ρ)
                  (<₊SumLeft (L₁ ·₊ κ) ρ)
                  (IsLipschitzWith.pres≈ (f-lipA z) x y κ x≈κy)
            in
            ∣ ((L₁ ·₊ κ) +₊ δ₀
            , witness<
            , λ v → liftCloseness L₂ (f x) (f y) (f-lipB x) (f-lipB y) (L₁ ·₊ κ) base-close v δ₀)
            ∣₁)
        (PA.isRounded≈ x y ε x≈y)

      f₁ᴸ : L[ A' , F' ]
      f₁ᴸ = f₁ , ∣ L₁ , f₁-lipA ∣₁

      lift₂ : Σ[ h ∈ (⟨ ℭ A' ⟩ → (⟨ ℭ B' ⟩ → T)) ]
                IsLipschitzWith (snd (ℭ A')) h (snd F') L₁
      lift₂ = LiftA.liftLipschitzWith L₁ (fst f₁ᴸ) f₁-lipA

      f̄ : ⟨ ℭ A' ⟩ → ⟨ ℭ B' ⟩ → T
      f̄ = fst lift₂

      f̄-lipA : IsLipschitzWith (snd (ℭ A')) f̄ (snd F') L₁
      f̄-lipA = snd lift₂

      f̄-lipB : ∀ u → IsLipschitzWith (snd (ℭ B')) (f̄ u) (snd T') L₂
      f̄-lipB = Elimℭ-Prop.go e
        where
        open import Cubical.Relation.Premetric.Completion.Elim A'

        e : Elimℭ-Prop (λ u → IsLipschitzWith (snd (ℭ B')) (f̄ u) (snd T') L₂)
        e .Elimℭ-Prop.ιA x = f₁-lipB x
        e .Elimℭ-Prop.limA x xc IH =
          subst
            (λ h → IsLipschitzWith (snd (ℭ B')) h (snd T') L₂)
            l≡f̄lim
            (limLipschitz (ℭ B') T' T-complete L₂ s s-cauchy (IH ∘ (_/ L₁)))
          where
          s : ℚ₊ → ⟨ ℭ B' ⟩ → T
          s = (f̄ ∘ x) ∘ (_/ L₁)

          s-cauchy : FTheory.isCauchy s
          s-cauchy ε δ =
            PF.subst≈ (s ε) (s δ)
              {ε = L₁ ·₊ (ε / L₁ +₊ δ / L₁)}
              {ε' = ε +₊ δ}
              (ℚ.·DistL+ ⟨ L₁ ⟩₊ ⟨ ε / L₁ ⟩₊ ⟨ δ / L₁ ⟩₊
              ∙ cong₂ ℚ._+_ (·/ L₁ ε) (·/ L₁ δ))
              (IsLipschitzWith.pres≈ f̄-lipA
                (x (ε / L₁)) (x (δ / L₁)) (ε / L₁ +₊ δ / L₁)
                (xc (ε / L₁) (δ / L₁)))

          f̄-s-lim : FTheory.isLimit s (f̄ (lim x xc))
          f̄-s-lim ε δ =
            PF.subst≈ (s ε) (f̄ (lim x xc))
              {ε = L₁ ·₊ (ε / L₁ +₊ δ / L₁)}
              {ε' = ε +₊ δ}
              (ℚ.·DistL+ ⟨ L₁ ⟩₊ ⟨ ε / L₁ ⟩₊ ⟨ δ / L₁ ⟩₊
              ∙ cong₂ ℚ._+_ (·/ L₁ ε) (·/ L₁ δ))
              (IsLipschitzWith.pres≈ f̄-lipA
                (x (ε / L₁)) (lim x xc) (ε / L₁ +₊ δ / L₁)
                (isLimitLim A' x xc (ε / L₁) (δ / L₁)))

          l≡f̄lim : fst (F-complete s s-cauchy) ≡ f̄ (lim x xc)
          l≡f̄lim = cong fst (FTheory.isPropLimit s (F-complete s s-cauchy) (f̄ (lim x xc) , f̄-s-lim))
        e .Elimℭ-Prop.isPropA u =
          isPropIsLipschitzWith (snd (ℭ B')) (f̄ u) (snd T') L₂

    liftBinary∘ι∘ι :
      ∀ (L₁ L₂ : ℚ₊) (f : A → B → T)
      (f-lipA : ∀ y → IsLipschitzWith (snd A') (λ x → f x y) (snd T') L₁)
      (f-lipB : ∀ x → IsLipschitzWith (snd B') (f x) (snd T') L₂)
      → (λ x y → fst (liftLipschitzBinaryWith L₁ L₂ f f-lipA f-lipB) (ι x) (ι y)) ≡ f
    liftBinary∘ι∘ι L₁ L₂ f f-lipA f-lipB =
      funExt λ x → funExt λ y → refl

-- It is quite common to have the codomain of the form ℭN, therefore here we specialize
-- the proof/constuctions above, avoiding to supply isCompleteℭ every time.

module LiftLipschitzℭ (M' : PremetricSpace ℓM ℓM') (N' : PremetricSpace ℓN' ℓN) where
  open LiftLipschitzCompleteCodomain M' (ℭ N') (isCompleteℭ N') public renaming (
      liftLipschitzWith to liftLipschitzWithℭ
    ; liftLipschitzWithFun to liftLipschitzWithFunℭ
    ; isLipschitzLiftLipschitzWith to isLipschitzLiftLipschitzWithℭ
    ; liftLipschitzExtension to liftLipschitzExtensionℭ
    ; liftLipschitz to liftLipschitzℭ
    ; liftLipschitzFun to liftLipschitzFunℭ
    ; lift∘ι to liftℭ∘ι)

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
  open LiftLipschitzCompleteCodomain M M isCompM

  L[id] : L[ ℭ M , M ]
  L[id] = liftLipschitz idᴸ

  M≅ℭM : Iso ⟨ M ⟩ ⟨ℭ M ⟩
  M≅ℭM .fun      = ι
  M≅ℭM .inv      = fst L[id]
  M≅ℭM .rightInv = funExt⁻ $ cong fst $
    lipschitz≡ _ _ (ιᴸ ∘L L[id]) idᴸ (cong ((ι {M' = M}) ∘_) (lift∘ι idᴸ))
  M≅ℭM .leftInv  = funExt⁻ (lift∘ι idᴸ)

-- This theorem needs the relation ≈ and the underlying type ⟨ M ⟩ to live in the same
-- universe to be well-typed if we want to state it without using `Lift`s:
-- Theorem 3.21
isComplete→≡ℭ : ∀ {ℓ} {M : PremetricSpace ℓ ℓ} → isComplete M → ⟨ M ⟩ ≡ ⟨ℭ M ⟩
isComplete→≡ℭ = ua ∘ isComplete→≃ℭ

isIdempotentℭ : ∀ {ℓ} {M : PremetricSpace ℓ ℓ} → ⟨ℭ M ⟩ ≡ ⟨ℭ ℭ M ⟩
isIdempotentℭ = isComplete→≡ℭ (isCompleteℭ _)

isComplete→CatIsoⁿ : ∀ {ℓ} {M : PremetricSpace ℓ ℓ} → isComplete M → CatIso (PrSpacesⁿ ℓ ℓ) M (ℭ M)
isComplete→CatIsoⁿ {M = M} isCompM = ιⁿ , isiso invⁿ sec ret
  where
  open LiftLipschitzCompleteCodomain M M isCompM
  module PM = PremetricStr (M .snd)

  id-lip1 : IsLipschitzWith (M .snd) (idfun ⟨ M ⟩) (M .snd)
            (1 , OrderedCommRingStr.0<1 (str ℚOrderedCommRing))
  IsLipschitzWith.pres≈ id-lip1 x y ε =
    PM.subst≈ x y (sym (ℚ.·IdL ⟨ ε ⟩₊))

  lift1 : Σ[ f ∈ (⟨ℭ M ⟩ → ⟨ M ⟩) ]
            IsLipschitzWith ((ℭ M) .snd) f (M .snd)
              (1 , OrderedCommRingStr.0<1 (str ℚOrderedCommRing))
  lift1 = liftLipschitzWith
    (1 , OrderedCommRingStr.0<1 (str ℚOrderedCommRing)) (idfun _) id-lip1

  lift1∘ι : fst lift1 ∘ ι ≡ idfun _
  lift1∘ι = refl

  invⁿ : NE[ ℭ M , M ]
  fst invⁿ = fst lift1
  IsNonExpanding.pres≈ (snd invⁿ) x y ε =
    PM.subst≈ (fst lift1 x) (fst lift1 y) (ℚ.·IdL ⟨ ε ⟩₊)
      ∘ IsLipschitzWith.pres≈ (snd lift1) x y ε

  sec : invⁿ ⋆⟨ PrSpacesⁿ _ _ ⟩ ιⁿ ≡ idⁿ
  sec = nonExpanding≡ M (ℭ M) (ιⁿ ∘NE invⁿ) idⁿ (cong ((ι {M' = M}) ∘_) lift1∘ι)

  ret : ιⁿ ⋆⟨ PrSpacesⁿ _ _ ⟩ invⁿ ≡ idⁿ
  ret = NE≡ lift1∘ι

isComplete→≡ℭ-PM : ∀ {ℓ} {M : PremetricSpace ℓ ℓ} → isComplete M → M ≡ ℭ M
isComplete→≡ℭ-PM {M = M} = isUnivalent.CatIsoToPath isUnivalentPrSpacesⁿ ∘ isComplete→CatIsoⁿ {M = M}

isIdempotentℭ-PM : ∀ {ℓ} {M : PremetricSpace ℓ ℓ} → ℭ M ≡ ℭ (ℭ M)
isIdempotentℭ-PM = isComplete→≡ℭ-PM (isCompleteℭ _)

module CompletionFunctor (ℓ : Level) where

  -- `PrSpacesⁿ` is univalent, which is enough to derive the generalized
  -- Theorem 3.21 above as an equality of premetric spaces:
  -- `isComplete→≡ℭ-PM` and `isIdempotentℭ-PM`.
  -- Univalence of `PrSpacesᴸ` is a separate question.

  open Functor
  open NatTrans
  open NatTransP
  open IsMonad
  open LiftLipschitzℭ

  -- The act on maps M → N is given by:
  -- 1) postcomposition with ι : N → ℭN, to get a map M → ℭN
  -- 2) Lift of the map M → ℭN, to get ℭM → ℭN

  ℭ⟨_⟩ : {M N : PremetricSpace ℓ ℓ} → L[ M , N ] → L[ ℭ M , ℭ N ]
  ℭ⟨_⟩ = liftLipschitzℭ _ _ ∘ (ιᴸ ∘L_)

  ℭ⟪_⟫ : {M N : PremetricSpace ℓ ℓ} → L[ M , N ] → ⟨ℭ M ⟩ → ⟨ℭ N ⟩
  ℭ⟪_⟫ = fst ∘ ℭ⟨_⟩

  ℭFunctor : Functor (PrSpacesᴸ ℓ ℓ) (PrSpacesᴸ ℓ ℓ)
  F-ob  ℭFunctor = ℭ
  F-hom ℭFunctor = ℭ⟨_⟩
  F-id  ℭFunctor = lipschitz≡ _ (ℭ _) _ _ refl
  F-seq ℭFunctor = λ fᴸ@(f , _) gᴸ@(g , _) → lipschitz≡ _ (ℭ _) _ _ $
    ℭ⟪ gᴸ ∘L fᴸ ⟫ ∘ ι     ≡⟨ liftℭ∘ι _ _ (ιᴸ ∘L (gᴸ ∘L fᴸ)) ⟩
    ι ∘ g ∘ f             ≡⟨ sym $ cong (_∘ f) (liftℭ∘ι _ _ (ιᴸ ∘L gᴸ)) ⟩
    ℭ⟪ gᴸ ⟫ ∘ ι ∘ f       ≡⟨ sym $ cong (ℭ⟪ gᴸ ⟫ ∘_) (liftℭ∘ι _ _ (ιᴸ ∘L fᴸ)) ⟩
    ℭ⟪ gᴸ ⟫ ∘ ℭ⟪ fᴸ ⟫ ∘ ι ∎


  ιᴸnat : 𝟙⟨ PrSpacesᴸ ℓ ℓ ⟩ ⇒ ℭFunctor
  N-ob  ιᴸnat = λ _ → ιᴸ
  N-hom ιᴸnat = sym ∘ L≡ ∘ liftℭ∘ι _ _ ∘ (ιᴸ ∘L_)

  --   M ––––– f –––––→ N
  --   |                |
  -- ι⟨ M ⟩     ↺     ι⟨ N ⟩
  --   ↓                ↓
  --  ℭ M ––– ℭ⟨ f ⟩ –→ ℭ N

  μᴸ⟨_⟩ : (M : PremetricSpace ℓ ℓ) → L[ ℭ (ℭ M) , ℭ M ]
  μᴸ⟨ _ ⟩ = liftLipschitzℭ _ _ idᴸ

  μᴸ⟪_⟫ : (M : PremetricSpace ℓ ℓ) → ⟨ℭ ℭ M ⟩ → ⟨ℭ M ⟩
  μᴸ⟪_⟫ = fst ∘ μᴸ⟨_⟩

  μᴸ : (ℭFunctor ∘F ℭFunctor) ⇒ ℭFunctor
  N-ob  μᴸ = μᴸ⟨_⟩
  N-hom μᴸ = λ f → lipschitz≡ _ (ℭ _) _ _ $
    μᴸ⟪ _ ⟫ ∘ ℭ⟪ ℭ⟨ f ⟩ ⟫ ∘ ι  ≡⟨ cong (μᴸ⟪ _ ⟫ ∘_) (liftℭ∘ι _ _ (ιᴸ ∘L ℭ⟨ f ⟩)) ⟩
    μᴸ⟪ _ ⟫ ∘ ι ∘ ℭ⟪ f ⟫      ≡⟨ cong (_∘ ℭ⟪ f ⟫) (liftℭ∘ι _ _ idᴸ) ⟩
    idfun _ ∘ ℭ⟪ f ⟫          ≡⟨⟩
    ℭ⟪ f ⟫ ∘ idfun _          ≡⟨ sym $ cong (ℭ⟪ f ⟫ ∘_) (liftℭ∘ι _ _ idᴸ) ⟩
    ℭ⟪ f ⟫ ∘ μᴸ⟪ _ ⟫ ∘ ι      ∎

  -- ℭℭ M ––– ℭℭ⟨ f ⟩ ––→ ℭℭ N
  --   |                    |
  -- μ⟨ M ⟩      ↺        μ⟨ N ⟩
  --   ↓                    ↓
  --  ℭ M –––– ℭ⟨ f ⟩ –––→ ℭ N

  --  ℭM –––––––ℭf–––––––– ℭN
  --  \ ↘ι              ι↙ /
  --   \   ℭℭM –ℭℭf→ ℭℭN  /
  -- id \   | μ      μ |  / id
  --     \  ↓          ↓ /
  --      ↘ℭM ––ℭf–→ ℭN↙

  isMonadℭ : IsMonad ℭFunctor
  isMonadℭ .η       = ιᴸnat
  isMonadℭ .μ       = μᴸ
  isMonadℭ .idl-μ   = makeNatTransPathP (F-rUnit {F = ℭFunctor}) refl
    (funExt λ M → toPathP (transportRefl _ ∙ L≡ (liftℭ∘ι _ _ idᴸ)))
  isMonadℭ .idr-μ   = makeNatTransPathP (F-lUnit {F = ℭFunctor}) refl
    (funExt λ M → toPathP (transportRefl _ ∙ (lipschitz≡ M (ℭ M) _ _ $
      μᴸ⟪ M ⟫ ∘ ℭ⟪ ιᴸ {M' = M} ⟫ ∘ ι ≡⟨ cong (μᴸ⟪ M ⟫ ∘_) (liftℭ∘ι _ _ (ιᴸ ∘L ιᴸ)) ⟩
      μᴸ⟪ M ⟫ ∘ ι ∘ ι                ≡⟨ cong (_∘ ι) (liftℭ∘ι _ _ idᴸ) ⟩
      idfun _ ∘ ι                    ∎)))
  isMonadℭ .assoc-μ = makeNatTransPathP (F-assoc {F = ℭFunctor}) refl
    (funExt λ M → toPathP (transportRefl _ ∙ (lipschitz≡ (ℭ (ℭ M)) (ℭ M) _ _ $
      μᴸ⟪ M ⟫ ∘ ℭ⟪ μᴸ⟨ M ⟩ ⟫ ∘ ι ≡⟨ cong (μᴸ⟪ M ⟫ ∘_) (liftℭ∘ι _ _ (ιᴸ ∘L μᴸ⟨ M ⟩)) ⟩
      μᴸ⟪ M ⟫ ∘ ι ∘ μᴸ⟪ M ⟫      ≡⟨ cong (_∘ μᴸ⟪ M ⟫) (liftℭ∘ι _ _ idᴸ) ⟩
      idfun _ ∘ μᴸ⟪ M ⟫          ≡⟨⟩
      μᴸ⟪ M ⟫ ∘ idfun _          ≡⟨ sym $ cong (μᴸ⟪ M ⟫ ∘_) (liftℭ∘ι _ _ idᴸ) ⟩
      μᴸ⟪ M ⟫ ∘ μᴸ⟪ ℭ M ⟫ ∘ ι    ∎)))

  ℭMonad : Monad (PrSpacesᴸ ℓ ℓ)
  fst ℭMonad = ℭFunctor
  snd ℭMonad = isMonadℭ
