{- This is a formalization of section 3.2 of "Formalising Real Numbers in Homotopy Type Theory", Gilbert -}
-- TO DO : correctly cite the paper
open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Properties {ℓ} {ℓ'}
  (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.NatPlusOne.Base as ℕ₊₁
open import Cubical.Data.Int.Fast.Base as ℤ hiding (_-_)

open import Cubical.Data.Rationals.Fast.Base as ℚ
import Cubical.Data.Rationals.Fast.Properties as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚ using () renaming (_<_ to _<ℚ_)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Binary.Properties

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast

open module 1/2∈ℚ = Charactersitic≠2 ℚOrderedCommRing [ 1 / 2 ] (eq/ _ _ refl)

open import Cubical.Reflection.RecordEquiv

open import Cubical.Tactics.CommRingSolver

private
  M = M' .fst
  ℚOCR = ℚOrderedCommRing
  ℚCR  = OrderedCommRing→CommRing ℚOCR
  open OrderedCommRingReasoning ℚOCR
  open OrderedCommRingTheory ℚOCR
  open IsSemigroup (SemigroupStr.isSemigroup (snd +ℚ₊Semigroup)) using () renaming (
    ·Assoc to +₊Assoc)
  open PremetricStr (M' .snd)
  open import Cubical.Relation.Premetric.Completion.Base M' renaming (ℭ to ℭM)
  open import Cubical.Relation.Premetric.Completion.Elim M'

  module _ (R : CommRing ℓ-zero) where
    open CommRingStr (snd R) using () renaming (_+_ to _+r_ ; _-_ to _-r_)
    lemma1 : ∀ x y z w → x +r y +r (z -r (y +r w)) ≡ (x +r z) -r w
    lemma1 x y z w = solve! R

    lemma2 : ∀ x y z w → x +r y +r (z -r (w +r y)) ≡ (x +r z) -r w
    lemma2 x y z w = solve! R

subst∼ : ∀ x y {ε ε'} → ⟨ ε ⟩₊ ≡ ⟨ ε' ⟩₊ → x ∼[ ε ] y → x ∼[ ε' ] y
subst∼ x y p = subst (x ∼[_] y) (ℚ₊≡ p)

ι-lim+₊ : ∀ x y ε δ yc → ι x ∼[ ε ] y δ → ι x ∼[ ε +₊ δ ] lim y yc
ι-lim+₊ x y ε δ yc p = ι-lim x y (ε +₊ δ) δ yc
  (≡₊→0< ε (plusMinus₊ ε δ))
  (subst∼ _ _ (sym (plusMinus₊ ε δ)) p)

lim-ι+₊ : ∀ x y ε δ xc → x δ ∼[ ε ] ι y → lim x xc ∼[ ε +₊ δ ] ι y
lim-ι+₊ x y ε δ xc p = lim-ι x y (ε +₊ δ) δ xc
  (≡₊→0< ε (plusMinus₊ ε δ))
  (subst∼ _ _ (sym (plusMinus₊ ε δ)) p)

lim-lim+₊ : ∀ x y ε δ η xc yc → x δ ∼[ ε ] y η → lim x xc ∼[ ε +₊ (δ +₊ η) ] lim y yc
lim-lim+₊ x y ε δ η xc yc p = lim-lim x y (ε +₊ (δ +₊ η)) δ η xc yc
  (≡₊→0< ε (plusMinus₊ ε (δ +₊ η)))
  (subst∼ _ _ (sym (plusMinus₊ ε (δ +₊ η))) p)

-- Lemma 3.5
isRefl∼ : ∀ x ε → x ∼[ ε ] x
isRefl∼ = Elimℭ-Prop.go λ where
  .Elimℭ-Prop.ιA      → λ x ε → ι-ι x x ε (isRefl≈ x ε)
  .Elimℭ-Prop.limA    → λ x xc IH ε →
    lim-lim x x ε (ε /4₊) (ε /4₊) xc xc (id-[/4+/4]₊ ε)
      ((IH (ε /4₊) (ε -₊ (ε /4₊ +₊ ε /4₊) , id-[/4+/4]₊ ε))
      :> x (ε /4₊) ∼[ ε -₊ (ε /4₊ +₊ ε /4₊) , _ ] x (ε /4₊))
  .Elimℭ-Prop.isPropA → λ _ → isPropΠ (λ _ → isProp∼ _ _ _)

-- lemma 3.6
isSetℭ : isSet ℭM
isSetℭ = reflPropRelImpliesIdentity→isSet
  (λ x y → ∀ ε → x ∼[ ε ] y) isRefl∼ (λ _ _ → isPropΠ (λ _ → isProp∼ _ _ _)) (eqℭ _ _)

-- lemma 3.7
isSym∼ : ∀ x y ε → x ∼[ ε ] y → y ∼[ ε ] x
isSym∼ _ _ ε (ι-ι x y .ε p)                 = ι-ι y x ε (isSym≈ x y ε p)
isSym∼ _ _ ε (ι-lim x y .ε δ yc Δ p)        = lim-ι y x ε δ yc Δ $
  isSym∼ (ι x) (y δ) (ε -₊ δ , Δ) p
isSym∼ _ _ ε (lim-ι x y .ε δ xc Δ p)        = ι-lim y x ε δ xc Δ $
  isSym∼ (x δ) (ι y) (ε -₊ δ , Δ) p
isSym∼ _ _ ε (lim-lim x y .ε δ η xc yc Δ p) = let
    lemma : ε -₊ (δ +₊ η) ≡ ε -₊ (η +₊ δ)
    lemma = cong (ℚ._-_ ⟨ ε ⟩₊) (ℚ.+Comm ⟨ δ ⟩₊ ⟨ η ⟩₊)
    Δ' : 0 <ℚ ε -₊ (η +₊ δ)
    Δ' = subst (0 <ℚ_) lemma Δ
  in
    lim-lim y x ε η δ yc xc Δ'
    (subst∼ (y η) (x δ) lemma (isSym∼ (x δ) (y η) (_ , Δ) p))
isSym∼ _ _ ε (isProp∼ x .ε y p q i)         = isProp∼ y ε x
  (isProp∼ y ε x (isSym∼ _ _ ε p) (isSym∼ _ _ ε q) i)
  (isProp∼ y ε x (isSym∼ _ _ ε p) (isSym∼ _ _ ε q) i) i

-- Definition 3.8
-- Balls : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
-- Balls = Σ[ B ∈ (ℚ₊ → ℭM → hProp (ℓ-max ℓ ℓ')) ]
--   (∀ ε y → ⟨ B ε y ⟩ ≃ (∃[ δ ∈ ℚ₊ ] (δ <₊ ε × ⟨ B δ y ⟩)))
--   × (∀ ε δ y z → y ∼[ ε ] z → ⟨ B δ y ⟩ → ⟨ B (ε +₊ δ) z ⟩)

-- Record Definition(?)
record IsBall (B : ℚ₊ → ℭM → Type (ℓ-max ℓ ℓ')) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  constructor isball
  field
    isPropBall       : ∀ ε y     → isProp (B ε y)
    isRoundedBall    : ∀ ε y     → B ε y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × B δ y
    isTriangularBall : ∀ ε δ y z → B ε y → y ∼[ δ ] z → B (ε +₊ δ) z

  isMonotoneBall< : ∀ y ε δ → ε <₊ δ → B ε y → B δ y
  isMonotoneBall< y ε δ ε<δ Bεy = subst (flip B y)
    (ℚ₊≡ (ℚ.+Comm ⟨ ε ⟩₊ (δ -₊ ε) ∙ minusPlus₊ δ ε)) $
    isTriangularBall ε [ δ -₊ ε ]⟨ ε<δ ⟩ y y
    (Bεy                         :> B ε y )
    (isRefl∼ y [ δ -₊ ε ]⟨ ε<δ ⟩ :>  y ∼[ [ δ -₊ ε ]⟨ ε<δ ⟩ ] y )

  isMonotoneBall≤ : ∀ y ε δ → ε ≤₊ δ → B ε y → B δ y
  isMonotoneBall≤ y ε δ ε≤δ Bεy with ⟨ ε ⟩₊ ℚ.≟ ⟨ δ ⟩₊
  ... | ℚ.lt ε<δ = isMonotoneBall< y ε δ ε<δ Bεy
  ... | ℚ.eq ε≡δ = subst (flip B y) (ℚ₊≡ ε≡δ) Bεy
  ... | ℚ.gt δ<ε = ⊥.rec (ℚ.isIrrefl< ⟨ ε ⟩₊ (ℚ.isTrans≤< ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟨ ε ⟩₊ ε≤δ δ<ε))

  isRoundedBall⁻ : ∀ ε y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (B δ y) → B ε y
  isRoundedBall⁻ ε y = PT.rec (isPropBall ε y) $
    uncurry λ δ → uncurry (isMonotoneBall< y δ ε)

  isRoundedBall≃ : ∀ ε y → (B ε y) ≃ (∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (B δ y))
  isRoundedBall≃ ε y = propBiimpl→Equiv
    (isPropBall _ _) squash₁ (isRoundedBall ε y) (isRoundedBall⁻ ε y)

unquoteDecl IsBallIsoΣ = declareRecordIsoΣ IsBallIsoΣ (quote IsBall)

Balls : Type (ℓ-suc (ℓ-max ℓ ℓ'))
Balls = Σ[ B ∈ (ℚ₊ → ℭM → Type (ℓ-max ℓ ℓ')) ] IsBall B

isPropIsBall : ∀ B → isProp (IsBall B)
isPropIsBall B = isOfHLevelRetractFromIso 1
  IsBallIsoΣ $
  isPropΣ (isPropΠ2 λ _ _ → isPropIsProp) λ isPropBall →
  isProp×
    (isPropΠ3 λ _ _ _ → squash₁)
    (isPropΠ6 λ _ _ _ _ _ _ → isPropBall _ _)

-- Idea: reassociate the sigma type (using IsBallIsoΣ) to prove that B and B'
-- can be seen as in B , B' : ℚ₊ → M → hProp _, then use isSetΠ2, isSethProp,
-- and isSetΣSndProp with isPropIsBall
-- isSetBalls : isSet Balls
-- isSetBalls (B , p) (B' , q) = {! isProp  !}

_≈ᴮ[_]_ : Balls → ℚ₊ → Balls → Type (ℓ-max ℓ ℓ')
(B , _) ≈ᴮ[ ε ] (B' , _) = ∀ δ y → (B δ y → B' (δ +₊ ε) y) × (B' δ y → B (δ +₊ ε) y)

isProp≈ᴮ : ∀ B B' ε → isProp (B ≈ᴮ[ ε ] B')
isProp≈ᴮ (B , isBallB) (B' , isBallB') ε =
  isPropΠ2 λ δ y → isProp× (isProp→ (B'.isPropBall _ _)) (isProp→ (B.isPropBall _ _))
  where
    module B  = IsBall isBallB
    module B' = IsBall isBallB'

-- Defintion 3.9
record IsUpperCut (U : ℚ₊ → Type (ℓ-max ℓ ℓ')) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  constructor isuppercut
  field
    isPropUpperCut    : ∀ ε → isProp (U ε)
    isRoundedUpperCut : ∀ ε → U ε → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × U δ

unquoteDecl IsUpperCutIsoΣ = declareRecordIsoΣ IsUpperCutIsoΣ (quote IsUpperCut)

UpperCuts : Type (ℓ-suc (ℓ-max ℓ ℓ'))
UpperCuts = Σ[ U ∈ (ℚ₊ → Type (ℓ-max ℓ ℓ')) ] IsUpperCut U

isPropIsUpperCut : ∀ U → isProp (IsUpperCut U)
isPropIsUpperCut U = isOfHLevelRetractFromIso 1
  IsUpperCutIsoΣ $
  isPropΣ (isPropΠ λ _ → isPropIsProp) λ _ →
    (isPropΠ2 λ _ _ → squash₁)

_≈ᵁ[_]_ : UpperCuts → ℚ₊ → UpperCuts → Type (ℓ-max ℓ ℓ')
(U , _) ≈ᵁ[ ε ] (U' , _) = ∀ δ → (U δ → U' (δ +₊ ε)) × (U' δ → U (δ +₊ ε))

isProp≈ᵁ : ∀ U U' ε → isProp (U ≈ᵁ[ ε ] U')
isProp≈ᵁ (U , isUpperCutU) (U' , isUpperCutU') ε =
  isPropΠ λ δ → isProp× (isProp→ (U'.isPropUpperCut _)) (isProp→ (U.isPropUpperCut _))
  where
    module U  = IsUpperCut isUpperCutU
    module U' = IsUpperCut isUpperCutU'

-- Lemma 3.10
isSeparated≈ᴮ : ∀ B B' → (∀ ε → B ≈ᴮ[ ε ] B') → B ≡ B'
isSeparated≈ᴮ (B , isBallB) (B' , isBallB') B≈B' = Σ≡Prop isPropIsBall $
  funExt λ ε → funExt λ y → hPropExt (B.isPropBall _ _) (B'.isPropBall _ _)
    (λ Bεy → flip (PT.rec (B'.isPropBall _ _)) (B.isRoundedBall ε y Bεy)
     λ (δ , δ<ε , Bδy) →
     subst (flip B' y) (ℚ₊≡ (ℚ.+Comm ⟨ δ ⟩₊ (ε -₊ δ) ∙ minusPlus₊ ε δ))
                       (fst (B≈B' [ ε -₊ δ ]⟨ δ<ε ⟩ δ y) Bδy) )
    (λ B'εy → flip (PT.rec (B.isPropBall _ _)) (B'.isRoundedBall ε y B'εy)
     λ (δ , δ<ε , B'δy) →
     subst (flip B  y) (ℚ₊≡ (ℚ.+Comm ⟨ δ ⟩₊ (ε -₊ δ) ∙ minusPlus₊ ε δ))
                       (snd (B≈B' [ ε -₊ δ ]⟨ δ<ε ⟩ δ y) B'δy))
  where
    module B  = IsBall isBallB
    module B' = IsBall isBallB'

-- Lemma 3.11
isSeparated≈ᵁ : ∀ U U' → (∀ ε → U ≈ᵁ[ ε ] U') → U ≡ U'
isSeparated≈ᵁ (U , isUpperCutU) (U' , isUpperCutU') U≈U' = Σ≡Prop isPropIsUpperCut $
  funExt λ ε → hPropExt (U.isPropUpperCut _) (U'.isPropUpperCut _)
    (λ Uε → flip (PT.rec (U'.isPropUpperCut _)) (U.isRoundedUpperCut _ Uε)
     λ (δ , δ<ε , Uδ) → subst U' (ℚ₊≡ (ℚ.+Comm ⟨ δ ⟩₊ (ε -₊ δ) ∙ minusPlus₊ ε δ))
                                 (fst (U≈U' [ ε -₊ δ ]⟨ δ<ε ⟩ δ) Uδ))
    (λ U'ε → flip (PT.rec (U.isPropUpperCut _)) (U'.isRoundedUpperCut _ U'ε)
     λ (δ , δ<ε , U'δ) → subst U (ℚ₊≡ (ℚ.+Comm ⟨ δ ⟩₊ (ε -₊ δ) ∙ minusPlus₊ ε δ))
                                 (snd (U≈U' [ ε -₊ δ ]⟨ δ<ε ⟩ δ) U'δ))
  where
    module U  = IsUpperCut isUpperCutU
    module U' = IsUpperCut isUpperCutU'

nonExpanding∼→≈ᵁ : (ℭM → UpperCuts) → Type (ℓ-max ℓ ℓ')
nonExpanding∼→≈ᵁ B = ∀ x y ε → x ∼[ ε ] y → B x ≈ᵁ[ ε ] B y

nonExpanding∼→≈ᴮ : (ℭM → Balls) → Type (ℓ-max ℓ ℓ')
nonExpanding∼→≈ᴮ B = ∀ x y ε → x ∼[ ε ] y → B x ≈ᴮ[ ε ] B y

-- Lemma 3.12
isNonExpanding∼→≈ᵁ→isBall : ∀ B → nonExpanding∼→≈ᵁ B → IsBall (λ ε y → fst (B y) ε)
isNonExpanding∼→≈ᵁ→isBall B isNE = isBall where
  open IsBall
  open IsUpperCut

  isBall : IsBall _
  isBall .isPropBall       = λ ε y → isPropUpperCut (snd (B y)) ε
  isBall .isRoundedBall    = λ ε y → isRoundedUpperCut (snd (B y)) ε
  isBall .isTriangularBall = λ ε δ y z ⟨By⟩ε y∼δz → fst (isNE y z δ y∼δz ε) ⟨By⟩ε

open Recℭ

BallsCenteredAtι[Rec] : M → Recℭ UpperCuts (flip ∘ _≈ᵁ[_]_)
BallsCenteredAtι[Rec] x .ιA y .fst = Lift {ℓ'} {ℓ} ∘ (x ≈[_] y)
BallsCenteredAtι[Rec] x .ιA y .snd = isUC where
  open IsUpperCut

  isUC : IsUpperCut _
  isUC .isPropUpperCut    = λ ε (lift p) (lift q) → cong lift (isProp≈ x y ε p q)
  isUC .isRoundedUpperCut = λ ε (lift p) → PT.map (λ (δ , δ<ε , q) → (δ , δ<ε , lift q))
                                                  (isRounded≈ x y ε p)
BallsCenteredAtι[Rec] x .limA Bx,y_ _ .fst =
  λ ε → ∃[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ] fst (Bx,y δ) [ ε -₊ δ ]⟨ δ<ε ⟩
BallsCenteredAtι[Rec] x .limA Bx,y_ _ .snd = isUC where
  open IsUpperCut

  isUC : IsUpperCut _
  isUC .isPropUpperCut    = λ ε → squash₁
  isUC .isRoundedUpperCut = λ ε → PT.rec squash₁ λ (δ , δ<ε , B[ε-δ]x,yδ) →
    let
    ∃η : ∃[ η ∈ ℚ₊ ] (η <₊ [ ε -₊ δ ]⟨ δ<ε ⟩) × fst (Bx,y δ) η
    ∃η = By.isRoundedUpperCut δ [ ε -₊ δ ]⟨ δ<ε ⟩ B[ε-δ]x,yδ
    in
    flip PT.map ∃η λ (η , η<ε-δ , B[η]x,yδ) →
    let
    η+δ<ε = subst (⟨ η +₊ δ ⟩₊ <ℚ_) (minusPlus₊ ε δ) (ℚ.<-+o ⟨ η ⟩₊ (ε -₊ δ) ⟨ δ ⟩₊ η<ε-δ)
    B[η+δ-δ]x,yδ = subst (fst (Bx,y δ)) (ℚ₊≡ (sym (plusMinus₊ η δ))) B[η]x,yδ
    in
    (η +₊ δ) , η+δ<ε , ∣ δ , <₊SumRight δ η , B[η+δ-δ]x,yδ ∣₁
    where
      module By (η : ℚ₊) = IsUpperCut (snd (Bx,y η))
BallsCenteredAtι[Rec] x .eqA       = isSeparated≈ᵁ
BallsCenteredAtι[Rec] x .ι-ι-B y z ε y≈z δ .fst (lift x≈y) =
  lift (isTriangular≈ x y z δ ε x≈y y≈z)
BallsCenteredAtι[Rec] x .ι-ι-B y z ε y≈z δ .snd (lift x≈z) =
  lift (isTriangular≈ x z y δ ε x≈z (isSym≈ y z ε y≈z))
BallsCenteredAtι[Rec] x .ι-lim-B y Bx,z_ ε δ _ Δ Bx,y≈ᵁBx,zδ η .fst (lift x≈y) =
  ∣ δ , δ<η+ε , B[η+ε-δ]x,zδ ∣₁
  where
    δ<η+ε : δ <₊ (η +₊ ε)
    δ<η+ε = begin<
      ⟨ δ ⟩₊      <⟨ 0<-→< ⟨ δ ⟩₊ ⟨ ε ⟩₊ Δ ⟩
      ⟨ ε ⟩₊      <⟨ <₊SumRight ε η ⟩
      ⟨ η +₊ ε ⟩₊ ◾

    B[η+ε-δ]x,zδ : fst (Bx,z δ) [ (η +₊ ε) -₊ δ ]⟨ δ<η+ε ⟩
    B[η+ε-δ]x,zδ = subst (fst (Bx,z δ)) (ℚ₊≡ (ℚ.+Assoc ⟨ η ⟩₊ ⟨ ε ⟩₊ _))
                                        (fst (Bx,y≈ᵁBx,zδ η) (lift x≈y))
BallsCenteredAtι[Rec] x .ι-lim-B y Bx,z_ ε δ Bx,zc Δ Bx,y≈ᵁBx,zδ η .snd B[η]x,limz =
  subst (Lift {ℓ'} {ℓ} ∘ (x ≈[_] y)) η+δ+ε-δ≡η+ε x≈[η+δ+ε-δ]y
  where
    module Bz (η : ℚ₊) = IsUpperCut (snd (Bx,z η))

    Bx,zc→ : ∀ ε' δ' η' → fst (Bx,z ε') η' → fst (Bx,z δ') (η' +₊ (ε' +₊ δ'))
    Bx,zc→ ε' δ' η' = fst (Bx,zc ε' δ' η')

    B[η+δ]x,zδ : fst (Bx,z δ) (η +₊ δ)
    B[η+δ]x,zδ = flip (PT.rec (Bz.isPropUpperCut δ (η +₊ δ))) B[η]x,limz λ
      { (δ' , δ'<η , B[η-δ']x,zδ') →
        let
          B[η-δ'+δ'+δ]x,zδ = Bx,zc→ δ' δ [ η -₊ δ' ]⟨ δ'<η ⟩ B[η-δ']x,zδ'

          η-δ'+δ'+δ≡η+δ : [ η -₊ δ' ]⟨ δ'<η ⟩ +₊ (δ' +₊ δ) ≡ η +₊ δ
          η-δ'+δ'+δ≡η+δ = ℚ₊≡ $ ℚ.+Assoc (η -₊ δ') _ _ ∙ cong (ℚ._+ _) (minusPlus₊ η δ')
        in
          subst (fst (Bx,z δ)) η-δ'+δ'+δ≡η+δ B[η-δ'+δ'+δ]x,zδ }

    Bx,zδ→x≈[+ε-δ]y : ∀ ξ → fst (Bx,z δ) ξ → Lift {ℓ'} {ℓ} (x ≈[ ξ +₊ ((ε -₊ δ) , Δ) ] y)
    Bx,zδ→x≈[+ε-δ]y = λ ξ → snd (Bx,y≈ᵁBx,zδ ξ)

    x≈[η+δ+ε-δ]y : Lift {ℓ'} {ℓ} (x ≈[ (η +₊ δ) +₊ ((ε -₊ δ) , Δ) ] y)
    x≈[η+δ+ε-δ]y = Bx,zδ→x≈[+ε-δ]y (η +₊ δ) B[η+δ]x,zδ

    η+δ+ε-δ≡η+ε : (η +₊ δ) +₊ ((ε -₊ δ) , Δ) ≡ η +₊ ε
    η+δ+ε-δ≡η+ε = ℚ₊≡ $
      ⟨ η +₊ δ ⟩₊ ℚ.+ (ε -₊ δ)         ≡⟨ sym $ ℚ.+Assoc ⟨ η ⟩₊ ⟨ δ ⟩₊ (ε -₊ δ) ⟩
      ⟨ η ⟩₊ ℚ.+ (⟨ δ ⟩₊ ℚ.+ (ε -₊ δ)) ≡⟨ cong (⟨ η ⟩₊ ℚ.+_) (ℚ.+Comm ⟨ δ ⟩₊ (ε -₊ δ)) ⟩
      ⟨ η ⟩₊ ℚ.+ ((ε -₊ δ) ℚ.+ ⟨ δ ⟩₊) ≡⟨ cong (⟨ η ⟩₊ ℚ.+_) (minusPlus₊ ε δ) ⟩
      ⟨ η +₊ ε ⟩₊                      ∎
BallsCenteredAtι[Rec] x .lim-ι-B Bx,y_ z ε δ Bx,yc Δ Bx,yδ≈ᵁBx,z η .fst B[η]x,limy =
  subst (Lift {ℓ'} {ℓ} ∘ (x ≈[_] z)) η+δ+ε-δ≡η+ε x≈[η+δ+ε-δ]z
  where
    module By (η : ℚ₊) = IsUpperCut (snd (Bx,y η))

    Bx,yc→ : ∀ ε' δ' η' → fst (Bx,y ε') η' → fst (Bx,y δ') (η' +₊ (ε' +₊ δ'))
    Bx,yc→ ε' δ' η' = fst (Bx,yc ε' δ' η')

    B[η+δ]x,yδ : fst (Bx,y δ) (η +₊ δ)
    B[η+δ]x,yδ = flip (PT.rec (By.isPropUpperCut δ (η +₊ δ))) B[η]x,limy λ
      { (δ' , δ'<η , B[η-δ']x,yδ') →
        let
          B[η-δ'+δ'+δ]x,yδ = Bx,yc→ δ' δ [ η -₊ δ' ]⟨ δ'<η ⟩ B[η-δ']x,yδ'

          η-δ'+δ'+δ≡η+δ : [ η -₊ δ' ]⟨ δ'<η ⟩ +₊ (δ' +₊ δ) ≡ η +₊ δ
          η-δ'+δ'+δ≡η+δ = ℚ₊≡ $ ℚ.+Assoc (η -₊ δ') _ _ ∙ cong (ℚ._+ _) (minusPlus₊ η δ')
        in
          subst (fst (Bx,y δ)) η-δ'+δ'+δ≡η+δ B[η-δ'+δ'+δ]x,yδ }

    Bx,yδ→x≈[+ε-δ]z : ∀ ξ → fst (Bx,y δ) ξ → Lift {ℓ'} {ℓ} (x ≈[ ξ +₊ ((ε -₊ δ) , Δ) ] z)
    Bx,yδ→x≈[+ε-δ]z = λ ξ → fst (Bx,yδ≈ᵁBx,z ξ)

    x≈[η+δ+ε-δ]z : Lift {ℓ'} {ℓ} (x ≈[ (η +₊ δ) +₊ ((ε -₊ δ) , Δ) ] z)
    x≈[η+δ+ε-δ]z = Bx,yδ→x≈[+ε-δ]z (η +₊ δ) B[η+δ]x,yδ

    η+δ+ε-δ≡η+ε : (η +₊ δ) +₊ ((ε -₊ δ) , Δ) ≡ η +₊ ε
    η+δ+ε-δ≡η+ε = ℚ₊≡ $
      ⟨ η +₊ δ ⟩₊ ℚ.+ (ε -₊ δ)         ≡⟨ sym $ ℚ.+Assoc ⟨ η ⟩₊ ⟨ δ ⟩₊ (ε -₊ δ) ⟩
      ⟨ η ⟩₊ ℚ.+ (⟨ δ ⟩₊ ℚ.+ (ε -₊ δ)) ≡⟨ cong (⟨ η ⟩₊ ℚ.+_) (ℚ.+Comm ⟨ δ ⟩₊ (ε -₊ δ)) ⟩
      ⟨ η ⟩₊ ℚ.+ ((ε -₊ δ) ℚ.+ ⟨ δ ⟩₊) ≡⟨ cong (⟨ η ⟩₊ ℚ.+_) (minusPlus₊ ε δ) ⟩
      ⟨ η +₊ ε ⟩₊                      ∎
BallsCenteredAtι[Rec] x .lim-ι-B Bx,y_ z ε δ Bx,yc Δ Bx,yδ≈ᵁBx,z η .snd (lift x≈z) =
  ∣ δ , δ<η+ε , B[η+ε-δ]x,yδ ∣₁
  where
    δ<η+ε : δ <₊ (η +₊ ε)
    δ<η+ε = begin<
      ⟨ δ ⟩₊      <⟨ 0<-→< ⟨ δ ⟩₊ ⟨ ε ⟩₊ Δ ⟩
      ⟨ ε ⟩₊      <⟨ <₊SumRight ε η ⟩
      ⟨ η +₊ ε ⟩₊ ◾

    B[η+ε-δ]x,yδ : fst (Bx,y δ) [ (η +₊ ε) -₊ δ ]⟨ δ<η+ε ⟩
    B[η+ε-δ]x,yδ = subst (fst (Bx,y δ)) (ℚ₊≡ (ℚ.+Assoc ⟨ η ⟩₊ ⟨ ε ⟩₊ _))
                                        (snd (Bx,yδ≈ᵁBx,z η) (lift x≈z))
BallsCenteredAtι[Rec] x .lim-lim-B Bx,y_ Bx,z_ ε δ η Bx,yc Bx,zc Δ Bx,yδ≈ᵁBx,zη θ .fst =
  PT.map λ (δ' , δ'<θ , B[θ-δ']x,yδ') →
    let

      B[θ-δ'+δ'+δ]x,yδ : fst (Bx,y δ) ([ θ -₊ δ' ]⟨ δ'<θ ⟩ +₊ (δ' +₊ δ))
      B[θ-δ'+δ'+δ]x,yδ = fst (Bx,yc δ' δ [ θ -₊ δ' ]⟨ δ'<θ ⟩) B[θ-δ']x,yδ'

      B[θ+δ]x,yδ : fst (Bx,y δ) (θ +₊ δ)
      B[θ+δ]x,yδ = flip (subst (fst (Bx,y δ))) B[θ-δ'+δ'+δ]x,yδ $ ℚ₊≡ $
        (θ -₊ δ') ℚ.+ ⟨ δ' +₊ δ ⟩₊       ≡⟨ ℚ.+Assoc (θ -₊ δ') ⟨ δ' ⟩₊ ⟨ δ ⟩₊ ⟩
        (θ -₊ δ') ℚ.+ ⟨ δ' ⟩₊ ℚ.+ ⟨ δ ⟩₊ ≡⟨ cong (ℚ._+ ⟨ δ ⟩₊) (minusPlus₊ θ δ') ⟩
        ⟨ θ +₊ δ ⟩₊                      ∎

      B[θ+δ+ε-[δ+η]]x,zη : fst (Bx,z η) (θ +₊ δ +₊ (ε -₊ (δ +₊ η) , Δ))
      B[θ+δ+ε-[δ+η]]x,zη = fst (Bx,yδ≈ᵁBx,zη (θ +₊ δ)) B[θ+δ]x,yδ

      η<θ+ε : η <₊ (θ +₊ ε)
      η<θ+ε = begin<
        ⟨ η ⟩₊         ≡→≤⟨ sym $ cong (ℚ._- ⟨ δ ⟩₊) (ℚ.+Comm ⟨ δ ⟩₊ _) ∙ plusMinus₊ η δ ⟩
        (δ +₊ η) -₊ δ   <⟨ Δ<₊ (δ +₊ η) δ ⟩
        ⟨ δ +₊ η ⟩₊      <⟨ 0<-→< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ Δ ⟩
        ⟨ ε ⟩₊           <⟨ <₊SumRight ε θ ⟩
        ⟨ θ +₊ ε ⟩₊      ◾

      B[θ+ε-η]x,zη : fst (Bx,z η) [ (θ +₊ ε) -₊ η ]⟨ η<θ+ε ⟩
      B[θ+ε-η]x,zη = flip (subst (fst (Bx,z η))) B[θ+δ+ε-[δ+η]]x,zη $ ℚ₊≡ $
        ⟨ θ +₊ δ ⟩₊ ℚ.+ (ε -₊ (δ +₊ η)) ≡⟨ lemma1 ℚCR ⟨ θ ⟩₊ ⟨ δ ⟩₊ ⟨ ε ⟩₊ ⟨ η ⟩₊ ⟩
        (θ +₊ ε) -₊ η                   ∎
    in
      η , η<θ+ε , B[θ+ε-η]x,zη
BallsCenteredAtι[Rec] x .lim-lim-B Bx,y_ Bx,z_ ε δ η Bx,yc Bx,zc Δ Bx,yδ≈ᵁBx,zη θ .snd =
  PT.map λ (δ' , δ'<θ , B[θ-δ']x,zδ') →
    let

      B[θ-δ'+δ'+η]x,zη : fst (Bx,z η) ([ θ -₊ δ' ]⟨ δ'<θ ⟩ +₊ (δ' +₊ η))
      B[θ-δ'+δ'+η]x,zη = fst (Bx,zc δ' η [ θ -₊ δ' ]⟨ δ'<θ ⟩) B[θ-δ']x,zδ'

      B[θ+η]x,zη : fst (Bx,z η) (θ +₊ η)
      B[θ+η]x,zη = flip (subst (fst (Bx,z η))) B[θ-δ'+δ'+η]x,zη $ ℚ₊≡ $
        (θ -₊ δ') ℚ.+ ⟨ δ' +₊ η ⟩₊       ≡⟨ ℚ.+Assoc (θ -₊ δ') ⟨ δ' ⟩₊ ⟨ η ⟩₊ ⟩
        (θ -₊ δ') ℚ.+ ⟨ δ' ⟩₊ ℚ.+ ⟨ η ⟩₊ ≡⟨ cong (ℚ._+ ⟨ η ⟩₊) (minusPlus₊ θ δ') ⟩
        ⟨ θ +₊ η ⟩₊                      ∎

      B[θ+η+ε-[δ+η]]x,yδ : fst (Bx,y δ) (θ +₊ η +₊ (ε -₊ (δ +₊ η) , Δ))
      B[θ+η+ε-[δ+η]]x,yδ = snd (Bx,yδ≈ᵁBx,zη (θ +₊ η)) B[θ+η]x,zη

      δ<θ+ε : δ <₊ (θ +₊ ε)
      δ<θ+ε = begin<
        ⟨ δ ⟩₊         ≡→≤⟨ sym $ plusMinus₊ δ η ⟩
        (δ +₊ η) -₊ η   <⟨ Δ<₊ (δ +₊ η) η ⟩
        ⟨ δ +₊ η ⟩₊      <⟨ 0<-→< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ Δ ⟩
        ⟨ ε ⟩₊           <⟨ <₊SumRight ε θ ⟩
        ⟨ θ +₊ ε ⟩₊      ◾

      B[θ+ε-δ]x,yδ : fst (Bx,y δ) [ (θ +₊ ε) -₊ δ ]⟨ δ<θ+ε ⟩
      B[θ+ε-δ]x,yδ = flip (subst (fst (Bx,y δ))) B[θ+η+ε-[δ+η]]x,yδ $ ℚ₊≡ $
        ⟨ θ +₊ η ⟩₊ ℚ.+ (ε -₊ (δ +₊ η)) ≡⟨ lemma2 ℚCR ⟨ θ ⟩₊ ⟨ η ⟩₊ ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟩
        (θ +₊ ε) -₊ δ                   ∎

    in
      δ , δ<θ+ε , B[θ+ε-δ]x,yδ
BallsCenteredAtι[Rec] x .isPropB   = isProp≈ᵁ

-- Defintion 3.13 (first part)
B⟨ι_,_⟩ : M → ℭM → UpperCuts
B⟨ι_,_⟩ = Recℭ.go ∘ BallsCenteredAtι[Rec]

B[_]⟨ι_,_⟩ : ℚ₊ → M → ℭM → Type (ℓ-max ℓ ℓ')
B[ ε ]⟨ι x , y ⟩ = fst B⟨ι x , y ⟩ ε

isNonExpanding∼→≈ᵁB⟨ι_,⟩ : ∀ (x : M) → nonExpanding∼→≈ᵁ B⟨ι x ,_⟩
isNonExpanding∼→≈ᵁB⟨ι_,⟩ x = λ y z ε → go∼ (BallsCenteredAtι[Rec] x)

B⟨ι_,⟩ : M → Balls
B⟨ι_,⟩ x .fst = B[_]⟨ι x ,_⟩
B⟨ι_,⟩ x .snd = isNonExpanding∼→≈ᵁ→isBall B⟨ι x ,_⟩ isNonExpanding∼→≈ᵁB⟨ι x ,⟩

{-
BallsCenteredAt[Rec] : Recℭ Balls (flip ∘ _≈ᴮ[_]_)
BallsCenteredAt[Rec] .ιA          = B⟨ι_,⟩
BallsCenteredAt[Rec] .limA Bx Bxc .fst = λ ε y →
  ∃[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ _ ] fst (Bx δ) [ ε -₊ δ ]⟨ δ<ε ⟩ y
BallsCenteredAt[Rec] .limA Bx Bxc .snd = isB where
  open IsBall
  open Elimℭ-Prop
  module Bx (η : ℚ₊) = IsBall (snd (Bx η))

  isB : IsBall _
  isB .isPropBall       = λ _ _ → squash₁
  isB .isRoundedBall    = λ ε y → PT.map λ (δ , δ<ε , B[ε-δ]xδ,y) →
    {!   !} , {!   !} , ∣ {!   !} , {!   !} , {!  !} ∣₁
  isB .isTriangularBall = λ ε δ y z → flip λ y∼z → PT.map λ (η , η<ε , B[ε-η]xη,y) →
    {!   !} , {!   !} , {!   !}
BallsCenteredAt[Rec] .eqA         = isSeparated≈ᴮ
BallsCenteredAt[Rec] .ι-ι-B       = {!    !}
BallsCenteredAt[Rec] .ι-lim-B     = {!    !}
BallsCenteredAt[Rec] .lim-ι-B     = {!   !}
BallsCenteredAt[Rec] .lim-lim-B   = {!   !}
BallsCenteredAt[Rec] .isPropB     = isProp≈ᴮ

-- Defintion 3.13 (second part)
B⟨_,⟩ : ℭM → Balls
B⟨_,⟩ = Recℭ.go BallsCenteredAt[Rec]

B[_]⟨_,_⟩ : ℚ₊ → ℭM → ℭM → Type (ℓ-max ℓ ℓ')
B[_]⟨_,_⟩ = flip (fst ∘ B⟨_,⟩)

isNonExpanding∼→≈ᴮB⟨,⟩ : nonExpanding∼→≈ᴮ B⟨_,⟩
isNonExpanding∼→≈ᴮB⟨,⟩ = λ _ _ _ → Recℭ.go∼ BallsCenteredAt[Rec]

-- Theorem 3.14
module _ where
  _ : ∀ {ε x y} → B[ ε ]⟨ ι x , ι y ⟩ ≡ Lift {ℓ'} {ℓ} (x ≈[ ε ] y)
  _ = refl

  _ : ∀ {ε x y yc} → B[ ε ]⟨ ι x , lim y yc ⟩
                 ≡ (∃[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ] B[ [ ε -₊ δ ]⟨ δ<ε ⟩ ]⟨ι x , y δ ⟩)
  _ = refl
  -- TO DO : other computations once BallsCenteredAt[Rec] is defined also for limit points

∼→B : ∀ {x y ε} → x ∼[ ε ] y → B[ ε ]⟨ x , y ⟩
∼→B = {!    !}

B→∼ : ∀ {x y ε} → B[ ε ]⟨ x , y ⟩ → x ∼[ ε ] y
B→∼ = {!   !}

-- Theorem 3.15
∼≃B : ∀ {x y ε} → (x ∼[ ε ] y) ≃ B[ ε ]⟨ x , y ⟩
∼≃B = propBiimpl→Equiv (isProp∼ _ _ _) (IsBall.isPropBall (snd B⟨ _ ,⟩) _ _) ∼→B B→∼

-- -}
