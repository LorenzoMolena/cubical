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
open import Cubical.Algebra.Ring
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
  ℚR   = OrderedCommRing→Ring ℚOCR
  open OrderedCommRingReasoning ℚOCR
  open OrderedCommRingTheory ℚOCR
  open RingTheory ℚR
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

    lemma3 : ∀ x y z w → (x -r y) +r (z -r w) ≡ (x +r z) -r (y +r w)
    lemma3 x y z w = solve! R

    lemma4 : ∀ x y z u v → (x -r (y +r z)) +r (z +r u) +r (v -r u) ≡ (x +r v) -r y
    lemma4 x y z u v = solve! R

    lemma5 : ∀ x y z u v w →
      (x -r (y +r z)) +r (z +r u) +r (v -r (u +r w)) ≡ (x +r v) -r (y +r w)
    lemma5 x y z u v w = solve! R

    lemma6 : ∀ x y z u v w →
      (x -r (y +r z)) +r (z +r u) +r (v -r (w +r u)) ≡ (x +r v) -r (y +r w)
    lemma6 x y z u v w = solve! R

    lemma7 : ∀ x y z w → ((x -r y) +r (y +r z)) +r (w -r z) ≡ x +r w
    lemma7 x y z w = solve! R

    lemma8 : ∀ x y z u v → ((x -r (y +r z)) +r (y +r u)) +r (v -r u) ≡ (x +r v) -r z
    lemma8 x y z u v = solve! R

    lemma9 : ∀ x y z u v → ((x -r y) +r (y +r z)) +r (u -r (z +r v)) ≡ (x +r u) -r v
    lemma9 x y z u v = solve! R

    lemma10 : ∀ x y z u v w →
      ((x -r (y +r z)) +r (y +r u)) +r (v -r (u +r w)) ≡ (x +r v) -r (w +r z)
    lemma10 x y z u v w = solve! R

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
isRefl∼ = Elimℭ-Prop.go e where
  e : Elimℭ-Prop (λ x → ∀ ε → x ∼[ ε ] x)
  Elimℭ-Prop.ιA      e x ε       = ι-ι x x ε (isRefl≈ x ε)
  Elimℭ-Prop.limA    e x xc IH ε =
    lim-lim x x ε (ε /4₊) (ε /4₊) xc xc (id-[/4+/4]₊ ε)
      ((IH (ε /4₊) (ε -₊ (ε /4₊ +₊ ε /4₊) , id-[/4+/4]₊ ε))
      :> x (ε /4₊) ∼[ ε -₊ (ε /4₊ +₊ ε /4₊) , _ ] x (ε /4₊))
    :>   lim x xc  ∼[ ε ]                         lim x xc
  Elimℭ-Prop.isPropA e = λ _ → isPropΠ (λ _ → isProp∼ _ _ _)

-- lemma 3.6
isSetℭ : isSet ℭM
isSetℭ = reflPropRelImpliesIdentity→isSet
  (λ x y → ∀ ε → x ∼[ ε ] y) isRefl∼ (λ _ _ → isPropΠ (λ _ → isProp∼ _ _ _)) (eqℭ _ _)

-- lemma 3.7
isSym∼ : ∀ x y ε → x ∼[ ε ] y → y ∼[ ε ] x
isSym∼ = λ _ _ _ → Recℭ∼.go∼ r where
  r : Recℭ∼ λ x y ε → y ∼[ ε ] x
  Recℭ∼.ι-ι-B     r x y ε x≈y             = ι-ι y x ε (isSym≈ x y ε x≈y)
  Recℭ∼.ι-lim-B   r x y ε δ yc Δ _ q      = lim-ι y x ε δ yc Δ q
  Recℭ∼.lim-ι-B   r x y ε δ xc Δ _ q      = ι-lim y x ε δ xc Δ q
  Recℭ∼.lim-lim-B r x y ε δ η xc yc Δ _ q =
    let
      p : ε -₊ (δ +₊ η) ≡ ε -₊ (η +₊ δ)
      p = cong (ℚ._-_ ⟨ ε ⟩₊) (ℚ.+Comm ⟨ δ ⟩₊ ⟨ η ⟩₊)

      Δ' : 0 <ℚ ε -₊ (η +₊ δ)
      Δ' = subst (0 <ℚ_) p Δ
    in
      lim-lim y x ε η δ yc xc Δ' (subst∼ (y η) (x δ) p q)
  Recℭ∼.isPropB   r x y ε                 = isProp∼ y ε x

-- Using isSym∼, we can introduce a variant for Casesℭ:

record CasesℭSym {ℓA} {ℓB} (A : Type ℓA)
              (B : A → A → ℚ₊ → Type ℓB) : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA        : M → A
    limA      : (x : ℚ₊ → ℭM) → ((δ ε : ℚ₊) → x δ ∼[ δ +₊ ε ] x ε) → A
    eqA       : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

    ι-ι-B     : ∀ x y ε
                → x ≈[ ε ] y
                → B (ιA x) (ιA y) ε
    ι-lim-B   : ∀ x y ε δ yc Δ
                → ι x ∼[ ε -₊ δ , Δ ] y δ
                → (a∘x : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B (a∘x ε') (a∘x δ') (ε' +₊ δ'))
                → B (ιA x) (a∘x δ) (ε -₊ δ , Δ)
                → B (ιA x) (limA y yc) ε
    lim-lim-B : ∀ x y ε δ η xc yc Δ
                → x δ ∼[ ε -₊ (δ +₊ η) , Δ ] y η
                → (a∘x : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B (a∘x ε') (a∘x δ') (ε' +₊ δ'))
                → (a∘y : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B (a∘y ε') (a∘y δ') (ε' +₊ δ'))
                → B (a∘x δ) (a∘y η) (ε -₊ (δ +₊ η) , Δ)
                → B (limA x xc) (limA y yc) ε
    isSymB    : ∀ a a' ε → B a a' ε → B a' a ε
    isPropB   : ∀ a a' ε → isProp (B a a' ε)

  private
    c : Casesℭ A B
    Casesℭ.ιA        c = ιA
    Casesℭ.limA      c = limA
    Casesℭ.eqA       c = eqA
    Casesℭ.ι-ι-B     c = ι-ι-B
    Casesℭ.ι-lim-B   c = ι-lim-B
    Casesℭ.lim-ι-B   c = λ x y ε δ xc Δ xδ∼y Bx Bxc Bxδ,y →
      isSymB (ιA y) (limA x xc) ε
        (ι-lim-B y x ε δ xc Δ
          (isSym∼ (x δ) (ι y) (ε -₊ δ , Δ) xδ∼y)
          Bx
          Bxc
          (isSymB (Bx δ) (ιA y) (ε -₊ δ , Δ) Bxδ,y))
    Casesℭ.lim-lim-B c = lim-lim-B
    Casesℭ.isPropB   c = isPropB

  go : ℭM → A
  go = Casesℭ.go c

  go∼ : {x y : ℭM} {ε : ℚ₊} → x ∼[ ε ] y → B (go x) (go y) ε
  go∼ = Casesℭ.go∼ c

-- Definition 3.8
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

_≈ᴮ[_]_ : Balls → ℚ₊ → Balls → Type (ℓ-max ℓ ℓ')
(B , _) ≈ᴮ[ ε ] (B' , _) = ∀ δ y → (B δ y → B' (δ +₊ ε) y) × (B' δ y → B (δ +₊ ε) y)

isProp≈ᴮ : ∀ B B' ε → isProp (B ≈ᴮ[ ε ] B')
isProp≈ᴮ (B , isBallB) (B' , isBallB') ε =
  isPropΠ2 λ δ y → isProp× (isProp→ (B'.isPropBall _ _)) (isProp→ (B.isPropBall _ _))
  where
    module B  = IsBall isBallB
    module B' = IsBall isBallB'

isSym≈ᴮ : ∀ B B' ε → B ≈ᴮ[ ε ] B' → B' ≈ᴮ[ ε ] B
isSym≈ᴮ B B' ε B≈B' δ y = fst Σ-swap-≃ (B≈B' δ y)

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

isSym≈ᵁ : ∀ U U' ε → U ≈ᵁ[ ε ] U' → U' ≈ᵁ[ ε ] U
isSym≈ᵁ U U' ε U≈U' δ = fst Σ-swap-≃ (U≈U' δ)

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

isBall→isUpperCut : (B : Balls) → ∀ y → IsUpperCut (flip (fst B) y)
isBall→isUpperCut B y = isUC where
  open IsBall
  open IsUpperCut

  isUC : IsUpperCut _
  isPropUpperCut    isUC = flip (isPropBall (snd B)) y
  isRoundedUpperCut isUC = flip (isRoundedBall (B .snd)) y

UpperCut≈ : (x y : M) → UpperCuts
fst (UpperCut≈ x y) = Lift {ℓ'} {ℓ} ∘ (x ≈[_] y)
snd (UpperCut≈ x y) = isUC where
  open IsUpperCut
  isUC : IsUpperCut _
  isPropUpperCut    isUC ε (lift p) (lift q) = cong lift (isProp≈ x y ε p q)
  isRoundedUpperCut isUC ε (lift p) = PT.map (λ (δ , δ<ε , q) → (δ , δ<ε , lift q))
                                             (isRounded≈ x y ε p)

UpperCut∃< : (U : ℚ₊ → UpperCuts) → UpperCuts
fst (UpperCut∃< U) ε = ∃[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ] fst (U δ) [ ε -₊ δ ]⟨ δ<ε ⟩
snd (UpperCut∃< U) = isUC∃< where
  module UC (η : ℚ₊) = IsUpperCut (snd (U η))
  open IsUpperCut

  isUC∃< : IsUpperCut _
  isPropUpperCut    isUC∃< _ = squash₁
  isRoundedUpperCut isUC∃< ε = PT.rec squash₁ λ (δ , δ<ε , Uδ[ε-δ]) →
    flip PT.map (UC.isRoundedUpperCut δ _ Uδ[ε-δ]) λ (ξ , ξ<ε-δ , Uδ[ξ]) →

      let
        δ<ξ+δ : δ <₊ (ξ +₊ δ)
        δ<ξ+δ = <₊SumRight δ ξ

        ξ+δ<ε : (ξ +₊ δ) <₊ ε
        ξ+δ<ε = begin<
          ⟨ ξ +₊ δ ⟩₊         <⟨ ℚ.<-+o ⟨ ξ ⟩₊ (ε -₊ δ) ⟨ δ ⟩₊ ξ<ε-δ ⟩
          ε -₊ δ ℚ.+ ⟨ δ ⟩₊ ≡→≤⟨ minusPlus₊ ε δ ⟩
          ⟨ ε ⟩₊              ◾

        Uδ[ξ+δ-δ] : fst (U δ) [ (ξ +₊ δ) -₊ δ ]⟨ δ<ξ+δ ⟩
        Uδ[ξ+δ-δ] = subst (fst (U δ)) (ℚ₊≡ (sym (plusMinus₊ ξ δ))) Uδ[ξ]

      in
        ξ +₊ δ , ξ+δ<ε , ∣ δ , δ<ξ+δ , Uδ[ξ+δ-δ] ∣₁

UpperCut∃₂< : (U : ℚ₊ → ℚ₊ → UpperCuts) → UpperCuts
fst (UpperCut∃₂< U) = λ ε →
  ∃[ δ ∈ ℚ₊ ] Σ[ η ∈ ℚ₊ ] Σ[ δ+η<ε ∈ _ ] fst (U δ η) [ ε -₊ (δ +₊ η) ]⟨ δ+η<ε ⟩
snd (UpperCut∃₂< U) = isUC∃₂< where
  module UC (δ η : ℚ₊) = IsUpperCut (snd (U δ η))
  open IsUpperCut

  isUC∃₂< : IsUpperCut _
  isPropUpperCut    isUC∃₂< ε = squash₁
  isRoundedUpperCut isUC∃₂< ε = PT.rec squash₁ λ (δ , η , δ+η<ε , Uδ,η[ε-[δ+η]]) →
    flip PT.map (UC.isRoundedUpperCut δ η _ Uδ,η[ε-[δ+η]]) λ (ξ , ξ<ε-[δ+η] , Uδ,η[ξ]) →
      let

        δ+η<ξ+δ+η : (δ +₊ η) <₊ (ξ +₊ (δ +₊ η))
        δ+η<ξ+δ+η = <₊SumRight (δ +₊ η) ξ

        ξ+δ+η<ε : (ξ +₊ (δ +₊ η)) <₊ ε
        ξ+δ+η<ε = begin<
          ⟨ ξ +₊ (δ +₊ η) ⟩₊                <⟨ ℚ.<-+o ⟨ ξ ⟩₊ _ _ ξ<ε-[δ+η] ⟩
          (ε -₊ (δ +₊ η)) ℚ.+ ⟨ δ +₊ η ⟩₊ ≡→≤⟨ minusPlus₊ ε (δ +₊ η) ⟩
          ⟨ ε ⟩₊                            ◾

        Uδ,η[ξ+δ+η-[δ+η]] : fst (U δ η) [ ξ +₊ (δ +₊ η) -₊ δ +₊ η ]⟨ δ+η<ξ+δ+η ⟩
        Uδ,η[ξ+δ+η-[δ+η]] =
          subst (fst (U δ η)) (ℚ₊≡ (sym (plusMinus₊ ξ (δ +₊ η)))) Uδ,η[ξ]

      in
        ξ +₊ (δ +₊ η) , ξ+δ+η<ε , ∣ δ , η , δ+η<ξ+δ+η , Uδ,η[ξ+δ+η-[δ+η]] ∣₁

UpperCut∃<→UpperCut∃₂< : ∀ U ε δ δ<ε →
  fst (UpperCut∃< (flip U δ)) [ ε -₊ δ ]⟨ δ<ε ⟩ → fst (UpperCut∃₂< U) ε
UpperCut∃<→UpperCut∃₂< U ε δ δ<ε = PT.map λ (η , η<ε-δ , U[ε-δ-η]η,δ) →
  let
    η+δ<ε : (η +₊ δ) <₊ ε
    η+δ<ε = begin<
      ⟨ η +₊ δ ⟩₊           <⟨ ℚ.<-+o ⟨ η ⟩₊ (ε -₊ δ) ⟨ δ ⟩₊ η<ε-δ ⟩
      (ε -₊ δ) ℚ.+ ⟨ δ ⟩₊ ≡→≤⟨ minusPlus₊ ε δ ⟩
      ⟨ ε ⟩₊                ◾

    U[ε-[η+δ]]η,δ : fst (U η δ) [ ε -₊ (η +₊ δ) ]⟨ η+δ<ε ⟩
    U[ε-[η+δ]]η,δ = flip (subst (fst (U η δ))) U[ε-δ-η]η,δ $ ℚ₊≡ $
      (ε -₊ δ) ℚ.- ⟨ η ⟩₊                 ≡⟨ sym $ ℚ.+Assoc ⟨ ε ⟩₊ (ℚ.- ⟨ δ ⟩₊) _ ⟩
      ⟨ ε ⟩₊ ℚ.+ ((ℚ.- ⟨ δ ⟩₊) ℚ.- ⟨ η ⟩₊) ≡⟨ cong (⟨ ε ⟩₊ ℚ.+_) (-Dist ⟨ δ ⟩₊ ⟨ η ⟩₊) ⟩
      ε -₊ (δ +₊ η)                       ≡⟨ cong (ℚ._-_ ⟨ ε ⟩₊) (ℚ.+Comm ⟨ δ ⟩₊ ⟨ η ⟩₊) ⟩
      ε -₊ (η +₊ δ)                       ∎

  in
    η , δ , η+δ<ε , U[ε-[η+δ]]η,δ

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
  isPropBall       isBall ε y                = isPropUpperCut (snd (B y)) ε
  isRoundedBall    isBall ε y                = isRoundedUpperCut (snd (B y)) ε
  isTriangularBall isBall ε δ y z ⟨By⟩ε y∼δz = fst (isNE y z δ y∼δz ε) ⟨By⟩ε

open RecℭSym

BallsAtι[Rec] : M → RecℭSym UpperCuts (flip ∘ _≈ᵁ[_]_)
ιA   (BallsAtι[Rec] x) y       = UpperCut≈ x y
limA (BallsAtι[Rec] x) Bx,y_ _ = UpperCut∃< Bx,y_
eqA  (BallsAtι[Rec] x)         = isSeparated≈ᵁ
fst  (ι-ι-B (BallsAtι[Rec] x) y z ε y≈z δ) (lift x≈y) =
  lift (isTriangular≈ x y z δ ε x≈y y≈z)
snd  (ι-ι-B (BallsAtι[Rec] x) y z ε y≈z δ) (lift x≈z) =
  lift (isTriangular≈ x z y δ ε x≈z (isSym≈ y z ε y≈z))
fst  (ι-lim-B (BallsAtι[Rec] x) y Bx,z_ ε δ Bx,zc Δ Bx,y≈ᵁBx,zδ η) (lift x≈y) =
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
snd  (ι-lim-B (BallsAtι[Rec] x) y Bx,z_ ε δ Bx,zc Δ Bx,y≈ᵁBx,zδ η) B[η]x,limz =
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
fst  (lim-lim-B (BallsAtι[Rec] x) Bx,y_ Bx,z_ ε δ η Bx,yc Bx,zc Δ Bx,yδ≈ᵁBx,zη θ) =
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
        ⟨ η ⟩₊      <⟨ <₊SumRight η δ ⟩
        ⟨ δ +₊ η ⟩₊ <⟨ 0<-→< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ Δ ⟩
        ⟨ ε ⟩₊      <⟨ <₊SumRight ε θ ⟩
        ⟨ θ +₊ ε ⟩₊ ◾

      B[θ+ε-η]x,zη : fst (Bx,z η) [ (θ +₊ ε) -₊ η ]⟨ η<θ+ε ⟩
      B[θ+ε-η]x,zη = flip (subst (fst (Bx,z η))) B[θ+δ+ε-[δ+η]]x,zη $ ℚ₊≡ $
        ⟨ θ +₊ δ ⟩₊ ℚ.+ (ε -₊ (δ +₊ η)) ≡⟨ lemma1 ℚCR ⟨ θ ⟩₊ ⟨ δ ⟩₊ ⟨ ε ⟩₊ ⟨ η ⟩₊ ⟩
        (θ +₊ ε) -₊ η                   ∎
    in
      η , η<θ+ε , B[θ+ε-η]x,zη
snd  (lim-lim-B (BallsAtι[Rec] x) Bx,y_ Bx,z_ ε δ η Bx,yc Bx,zc Δ Bx,yδ≈ᵁBx,zη θ) =
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
        ⟨ δ ⟩₊      <⟨ <₊SumLeft δ η ⟩
        ⟨ δ +₊ η ⟩₊ <⟨ 0<-→< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ Δ ⟩
        ⟨ ε ⟩₊      <⟨ <₊SumRight ε θ ⟩
        ⟨ θ +₊ ε ⟩₊ ◾

      B[θ+ε-δ]x,yδ : fst (Bx,y δ) [ (θ +₊ ε) -₊ δ ]⟨ δ<θ+ε ⟩
      B[θ+ε-δ]x,yδ = flip (subst (fst (Bx,y δ))) B[θ+η+ε-[δ+η]]x,yδ $ ℚ₊≡ $
        ⟨ θ +₊ η ⟩₊ ℚ.+ (ε -₊ (δ +₊ η)) ≡⟨ lemma2 ℚCR ⟨ θ ⟩₊ ⟨ η ⟩₊ ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟩
        (θ +₊ ε) -₊ δ                   ∎

    in
      δ , δ<θ+ε , B[θ+ε-δ]x,yδ
isSymB    (BallsAtι[Rec] x) = isSym≈ᵁ
isPropB   (BallsAtι[Rec] x) = isProp≈ᵁ

-- Defintion 3.13 (first part)
B⟨ι_,_⟩ : M → ℭM → UpperCuts
B⟨ι_,_⟩ = RecℭSym.go ∘ BallsAtι[Rec]

B[_]⟨ι_,_⟩ : ℚ₊ → M → ℭM → Type (ℓ-max ℓ ℓ')
B[ ε ]⟨ι x , y ⟩ = fst B⟨ι x , y ⟩ ε

isNonExpanding∼→≈ᵁB⟨ι_,⟩ : ∀ (x : M) → nonExpanding∼→≈ᵁ B⟨ι x ,_⟩
isNonExpanding∼→≈ᵁB⟨ι_,⟩ x y z ε = RecℭSym.go∼ (BallsAtι[Rec] x)

B⟨ι_,⟩ : M → Balls
fst B⟨ι x ,⟩ = B[_]⟨ι x ,_⟩
snd B⟨ι x ,⟩ = isNonExpanding∼→≈ᵁ→isBall B⟨ι x ,_⟩ isNonExpanding∼→≈ᵁB⟨ι x ,⟩

module _ (Bx : ℚ₊ → Balls) (Bxc : ∀ ε δ → Bx ε ≈ᴮ[ ε +₊ δ ] Bx δ) where

  module isBx (η : ℚ₊) = IsBall (snd (Bx η))
  open CasesℭSym

  BallsAtlim[Cases] : CasesℭSym UpperCuts (flip ∘ _≈ᵁ[_]_)
  ιA   BallsAtlim[Cases] y    = UpperCut∃< λ δ →
    flip (fst (Bx δ)) (ι y) , isBall→isUpperCut (Bx δ) (ι y)
  limA BallsAtlim[Cases] y yc = UpperCut∃₂< λ δ η →
    flip (fst (Bx δ)) (y η) , isBall→isUpperCut (Bx δ) (y η)
  eqA  BallsAtlim[Cases]      = isSeparated≈ᵁ
  fst (ι-ι-B BallsAtlim[Cases] y z ε y≈z δ) =
    PT.map λ (η , η<δ , B[δ-η]xη,y) →
      let

        η<δ+ε : η <₊ (δ +₊ ε)
        η<δ+ε = begin<
          ⟨ η ⟩₊      <⟨ η<δ ⟩
          ⟨ δ ⟩₊      <⟨ <₊SumLeft δ ε ⟩
          ⟨ δ +₊ ε ⟩₊ ◾

        B[δ-η+ε]xη,z : fst (Bx η) ([ δ -₊ η ]⟨ η<δ ⟩ +₊ ε) (ι z)
        B[δ-η+ε]xη,z = isBx.isTriangularBall η
          [ δ -₊ η ]⟨ η<δ ⟩ ε (ι y) (ι z) B[δ-η]xη,y (ι-ι y z ε y≈z)

        B[δ+ε-η]xη,z : fst (Bx η) [ δ +₊ ε -₊ η ]⟨ η<δ+ε ⟩ (ι z)
        B[δ+ε-η]xη,z = flip (subst (flip (fst (Bx η)) (ι z))) B[δ-η+ε]xη,z $ ℚ₊≡ $
          (δ -₊ η) ℚ.+ ⟨ ε ⟩₊                 ≡⟨ sym $ ℚ.+Assoc ⟨ δ ⟩₊ (ℚ.- ⟨ η ⟩₊) _ ⟩
          ⟨ δ ⟩₊ ℚ.+ ((ℚ.- ⟨ η ⟩₊) ℚ.+ ⟨ ε ⟩₊) ≡⟨ cong (ℚ._+_ ⟨ δ ⟩₊) (ℚ.+Comm _ ⟨ ε ⟩₊) ⟩
          ⟨ δ ⟩₊ ℚ.+ (ε -₊ η)                 ≡⟨ ℚ.+Assoc ⟨ δ ⟩₊ ⟨ ε ⟩₊ _ ⟩
          (δ +₊ ε) -₊ η                       ∎
      in
        η , η<δ+ε , B[δ+ε-η]xη,z
  snd (ι-ι-B BallsAtlim[Cases] y z ε y≈z δ) =
    PT.map λ (η , η<δ , B[δ-η]xη,z) →
      let

        η<δ+ε : η <₊ (δ +₊ ε)
        η<δ+ε = begin<
          ⟨ η ⟩₊      <⟨ η<δ ⟩
          ⟨ δ ⟩₊      <⟨ <₊SumLeft δ ε ⟩
          ⟨ δ +₊ ε ⟩₊ ◾

        B[δ-η+ε]xη,y : fst (Bx η) ([ δ -₊ η ]⟨ η<δ ⟩ +₊ ε) (ι y)
        B[δ-η+ε]xη,y = isBx.isTriangularBall η
          [ δ -₊ η ]⟨ η<δ ⟩ ε (ι z) (ι y) B[δ-η]xη,z (ι-ι z y ε (isSym≈ _ _ _ y≈z))

        B[δ+ε-η]xη,y : fst (Bx η) [ δ +₊ ε -₊ η ]⟨ η<δ+ε ⟩ (ι y)
        B[δ+ε-η]xη,y = flip (subst (flip (fst (Bx η)) (ι y))) B[δ-η+ε]xη,y $ ℚ₊≡ $
          (δ -₊ η) ℚ.+ ⟨ ε ⟩₊                 ≡⟨ sym $ ℚ.+Assoc ⟨ δ ⟩₊ (ℚ.- ⟨ η ⟩₊) _ ⟩
          ⟨ δ ⟩₊ ℚ.+ ((ℚ.- ⟨ η ⟩₊) ℚ.+ ⟨ ε ⟩₊) ≡⟨ cong (ℚ._+_ ⟨ δ ⟩₊) (ℚ.+Comm _ ⟨ ε ⟩₊) ⟩
          ⟨ δ ⟩₊ ℚ.+ (ε -₊ η)                 ≡⟨ ℚ.+Assoc ⟨ δ ⟩₊ ⟨ ε ⟩₊ _ ⟩
          (δ +₊ ε) -₊ η                       ∎

      in
        η , η<δ+ε , B[δ+ε-η]xη,y
  fst (ι-lim-B BallsAtlim[Cases] y z ε δ zc Δ y∼zδ _ _ _ η) =
    PT.map λ (θ , θ<η , B[η-θ]xθ,y) →
      let
        θ+δ<η+ε : (θ +₊ δ) <₊ (η +₊ ε)
        θ+δ<η+ε = begin<
          ⟨ θ +₊ δ ⟩₊ <⟨ +Mono< ⟨ θ ⟩₊ ⟨ η ⟩₊ _ _ θ<η (0<-→< ⟨ δ ⟩₊ ⟨ ε ⟩₊ Δ) ⟩
          ⟨ η +₊ ε ⟩₊ ◾

        B[η+ε-[θ+δ]]xθ,zδ : fst (Bx θ) [ (η +₊ ε) -₊ (θ +₊ δ) ]⟨ θ+δ<η+ε ⟩ (z δ)
        B[η+ε-[θ+δ]]xθ,zδ = subst (flip (fst (Bx θ)) (z δ))
          (ℚ₊≡ (lemma3 ℚCR ⟨ η ⟩₊ ⟨ θ ⟩₊ ⟨ ε ⟩₊ ⟨ δ ⟩₊))
          (isBx.isTriangularBall θ [ η -₊ θ ]⟨ θ<η ⟩ (ε -₊ δ , Δ)
            (ι y) (z δ)
          (B[η-θ]xθ,y
            :> fst (Bx θ) [ η -₊ θ ]⟨ θ<η ⟩ (ι y))
          (y∼zδ
            :> (ι y ∼[ (ε -₊ δ) , Δ ] z δ))
            :> Bx θ .fst ([ η -₊ θ ]⟨ θ<η ⟩ +₊ ((ε -₊ δ) , Δ)) (z δ))

      in
        θ , δ , θ+δ<η+ε , B[η+ε-[θ+δ]]xθ,zδ
  snd (ι-lim-B BallsAtlim[Cases] y z ε δ zc Δ y∼zδ _ _ _ η) =
    PT.map λ (ξ , ζ , ξ+ζ<η , B[η-[ξ+ζ]]xξ,zζ) →
      let
        ξ<η+ε : ξ <₊ (η +₊ ε)
        ξ<η+ε = begin<
          ⟨ ξ ⟩₊      <⟨ <₊SumLeft ξ ζ ⟩
          ⟨ ξ +₊ ζ ⟩₊ <⟨ ξ+ζ<η ⟩
          ⟨ η ⟩₊      <⟨ <₊SumLeft η ε ⟩
          ⟨ η +₊ ε ⟩₊ ◾

        B[η+ε-ξ]xξ,y : fst (Bx ξ) [ η +₊ ε -₊ ξ ]⟨ ξ<η+ε ⟩ (ι y)
        B[η+ε-ξ]xξ,y = subst (flip (fst (Bx ξ)) (ι y))
          (ℚ₊≡ (lemma4 ℚCR ⟨ η ⟩₊ ⟨ ξ ⟩₊ ⟨ ζ ⟩₊ ⟨ δ ⟩₊ ⟨ ε ⟩₊))
          (isBx.isTriangularBall ξ ([ η -₊ ξ +₊ ζ ]⟨ ξ+ζ<η ⟩ +₊ (ζ +₊ δ)) (ε -₊ δ , Δ)
            (z δ) (ι y)
          (isBx.isTriangularBall ξ [ η -₊ ξ +₊ ζ ]⟨ ξ+ζ<η ⟩ (ζ +₊ δ)
            (z ζ) (z δ)
          (B[η-[ξ+ζ]]xξ,zζ
            :> fst (Bx ξ) [ η -₊ ξ +₊ ζ ]⟨ ξ+ζ<η ⟩ (z ζ))
          (zc ζ δ
            :> (z ζ) ∼[ ζ +₊ δ ] (z δ))
            :> fst (Bx ξ) ([ η -₊ ξ +₊ ζ ]⟨ ξ+ζ<η ⟩ +₊ (ζ +₊ δ)) (z δ))
          (isSym∼ (ι y) (z δ) ((ε -₊ δ) , Δ) y∼zδ
            :> (z δ) ∼[ ε -₊ δ , Δ ] (ι y))
            :> fst (Bx ξ) ([ η -₊ ξ +₊ ζ ]⟨ ξ+ζ<η ⟩ +₊ (ζ +₊ δ) +₊ ((ε -₊ δ) , Δ)) (ι y))

      in
        ξ , ξ<η+ε , B[η+ε-ξ]xξ,y
  fst (lim-lim-B BallsAtlim[Cases] y z ε δ η yc zc Δ yδ∼zη _ _ _ _ _ θ) =
    PT.map λ (ξ , ζ , ξ+ζ<θ , B[θ-[ξ+ζ]]xξ,yζ) →
      let
        ξ+η<θ+ε : (ξ +₊ η) <₊ (θ +₊ ε)
        ξ+η<θ+ε = begin<
          ⟨ ξ +₊ η ⟩₊               <⟨ +Mono< ⟨ ξ ⟩₊ _ ⟨ η ⟩₊ _
                                      (<₊SumLeft ξ ζ) (<₊SumRight η δ) ⟩
          ⟨ (ξ +₊ ζ) +₊ (δ +₊ η) ⟩₊ <⟨ +Mono< ⟨ ξ +₊ ζ ⟩₊ ⟨ θ ⟩₊ ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊
                                      ξ+ζ<θ (0<-→< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ Δ) ⟩
          ⟨ θ +₊ ε ⟩₊               ◾

        B[θ+ε-[ξ+η]]xξ,zη : fst (Bx ξ) [ (θ +₊ ε) -₊ (ξ +₊ η) ]⟨ ξ+η<θ+ε ⟩ (z η)
        B[θ+ε-[ξ+η]]xξ,zη = subst (flip (fst (Bx ξ)) (z η))
          (ℚ₊≡ (lemma5 ℚCR ⟨ θ ⟩₊ ⟨ ξ ⟩₊ ⟨ ζ ⟩₊ ⟨ δ ⟩₊ ⟨ ε ⟩₊ ⟨ η ⟩₊))
          (isBx.isTriangularBall ξ
            ([ θ -₊ (ξ +₊ ζ) ]⟨ ξ+ζ<θ ⟩ +₊ (ζ +₊ δ)) (ε -₊ (δ +₊ η) , Δ)
            (y δ) (z η)
          (isBx.isTriangularBall ξ [ θ -₊ (ξ +₊ ζ) ]⟨ ξ+ζ<θ ⟩ (ζ +₊ δ)
            (y ζ) (y δ)
          (B[θ-[ξ+ζ]]xξ,yζ
            :> fst (Bx ξ) [ θ -₊ (ξ +₊ ζ) ]⟨ ξ+ζ<θ ⟩ (y ζ))
          (yc ζ δ
            :> (y ζ ∼[ ζ +₊ δ ] y δ))
            :> fst (Bx ξ) ([ θ -₊ ξ +₊ ζ ]⟨ ξ+ζ<θ ⟩ +₊ (ζ +₊ δ)) (y δ))
          (yδ∼zη
            :> y δ ∼[ ε -₊ (δ +₊ η) , Δ ] z η)
            :> fst (Bx ξ) ([ θ -₊ ξ +₊ ζ ]⟨ ξ+ζ<θ ⟩ +₊ (ζ +₊ δ) +₊ ((ε -₊ (δ +₊ η)) , Δ))
                    (z η))

      in
        ξ , η , ξ+η<θ+ε , B[θ+ε-[ξ+η]]xξ,zη
  snd (lim-lim-B BallsAtlim[Cases] y z ε δ η yc zc Δ yδ∼zη By Byc Bz Bzc Byδ≈Bzη θ) =
    PT.map λ (ξ , ζ , ξ+ζ<θ , B[θ-[ξ+ζ]]xξ,zζ) →
      let
        ξ+δ<θ+ε : (ξ +₊ δ) <₊ (θ +₊ ε)
        ξ+δ<θ+ε = begin<
          ⟨ ξ +₊ δ ⟩₊               <⟨ +Mono< ⟨ ξ ⟩₊ _ ⟨ δ ⟩₊ _
                                      (<₊SumLeft ξ ζ) (<₊SumLeft δ η) ⟩
          ⟨ (ξ +₊ ζ) +₊ (δ +₊ η) ⟩₊ <⟨ +Mono< ⟨ ξ +₊ ζ ⟩₊ ⟨ θ ⟩₊ ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊
                                      ξ+ζ<θ (0<-→< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ Δ) ⟩
          ⟨ θ +₊ ε ⟩₊               ◾

        B[θ+ε-[ξ+δ]]xξ,zδ : fst (Bx ξ) [ (θ +₊ ε) -₊ (ξ +₊ δ) ]⟨ ξ+δ<θ+ε ⟩ (y δ)
        B[θ+ε-[ξ+δ]]xξ,zδ = subst (flip (fst (Bx ξ)) (y δ))
          (ℚ₊≡ (lemma6 ℚCR ⟨ θ ⟩₊ ⟨ ξ ⟩₊ ⟨ ζ ⟩₊ ⟨ η ⟩₊ ⟨ ε ⟩₊ ⟨ δ ⟩₊))
          (isBx.isTriangularBall ξ
            ([ θ -₊ ξ +₊ ζ ]⟨ ξ+ζ<θ ⟩ +₊ (ζ +₊ η)) (ε -₊ (δ +₊ η) , Δ)
            (z η) (y δ)
          (isBx.isTriangularBall ξ [ θ -₊ ξ +₊ ζ ]⟨ ξ+ζ<θ ⟩ (ζ +₊ η)
            (z ζ) (z η)
          (B[θ-[ξ+ζ]]xξ,zζ
            :> fst (Bx ξ) [ θ -₊ ξ +₊ ζ ]⟨ ξ+ζ<θ ⟩ (z ζ))
          (zc ζ η
            :> z ζ ∼[ ζ +₊ η ] z η)
            :> fst (Bx ξ) ([ θ -₊ (ξ +₊ ζ) ]⟨ ξ+ζ<θ ⟩ +₊ (ζ +₊ η)) (z η))
          (isSym∼ (y δ) (z η) (ε -₊ (δ +₊ η) , Δ) yδ∼zη
            :> (z η ∼[ (ε -₊ (δ +₊ η)) , Δ ] y δ))
            :> fst (Bx ξ) ([ θ -₊ (ξ +₊ ζ) ]⟨ ξ+ζ<θ ⟩ +₊ (ζ +₊ η) +₊ (ε -₊ (δ +₊ η) , Δ))
                    (y δ))

      in
        ξ , δ , ξ+δ<θ+ε , B[θ+ε-[ξ+δ]]xξ,zδ
  isSymB    BallsAtlim[Cases] = isSym≈ᵁ
  isPropB   BallsAtlim[Cases] = isProp≈ᵁ

  B⟨limᴿ[_,_],_⟩ : ℭM → UpperCuts
  B⟨limᴿ[_,_],_⟩ = CasesℭSym.go BallsAtlim[Cases]

  isNonExpanding∼→≈ᵁB⟨limᴿ[_,_],⟩ : nonExpanding∼→≈ᵁ B⟨limᴿ[_,_],_⟩
  isNonExpanding∼→≈ᵁB⟨limᴿ[_,_],⟩ = λ _ _ _ → CasesℭSym.go∼ BallsAtlim[Cases]

  B⟨limᴿ[_,_],⟩ : Balls
  B⟨limᴿ[_,_],⟩ = _ ,
    isNonExpanding∼→≈ᵁ→isBall B⟨limᴿ[_,_],_⟩ isNonExpanding∼→≈ᵁB⟨limᴿ[_,_],⟩

B[_]⟨limᴿ[_,_],_⟩ : ℚ₊ → ∀ Bx (Bxc : ∀ ε δ → Bx ε ≈ᴮ[ ε +₊ δ ] Bx δ) → ℭM → Type _
B[_]⟨limᴿ[_,_],_⟩ ε Bx Bxc = fst (B⟨limᴿ[ Bx , Bxc ],⟩) ε

module _ (x y : M) (ε : ℚ₊) (x≈y : x ≈[ ε ] y) where
  open IsBall

  B⟨ι,⟩→B⟨ι,⟩ : ∀ z δ → B[ δ ]⟨ι x , z ⟩ → B[ δ +₊ ε ]⟨ι y , z ⟩
  B⟨ι,⟩→B⟨ι,⟩ = Elimℭ-Prop.go e where
    open Elimℭ-Prop

    e : Elimℭ-Prop λ z → (δ : ℚ₊) → B[ δ ]⟨ι x , z ⟩ → B[ δ +₊ ε ]⟨ι y , z ⟩
    ιA      e z δ (lift x≈z) =
      lift (subst≈ y z (ℚ.+Comm ⟨ ε ⟩₊ ⟨ δ ⟩₊) (
        isTriangular≈ y x z ε δ (isSym≈ x y ε x≈y
          :> (y ≈[ ε ] x))
        (x≈z
          :> (x ≈[ δ ] z))
          :> (y ≈[ ε +₊ δ ] z)))
    limA    e z zc Bx,z→By,z δ = PT.map λ (η , η<δ , B[δ-η]ιx,zη) →
      let
        η<δ+ε : η <₊ (δ +₊ ε)
        η<δ+ε = begin<
          ⟨ η ⟩₊      <⟨ η<δ ⟩
          ⟨ δ ⟩₊      <⟨ <₊SumLeft δ ε ⟩
          ⟨ δ +₊ ε ⟩₊ ◾

        B[δ+ε-η]ιy,zη : B[ [ (δ +₊ ε) -₊ η ]⟨ η<δ+ε ⟩ ]⟨ι y , z η ⟩
        B[δ+ε-η]ιy,zη = subst (B[_]⟨ι y , z η ⟩)
          (ℚ₊≡ $
            δ -₊ η ℚ.+ ⟨ ε ⟩₊                 ≡⟨ sym $ ℚ.+Assoc ⟨ δ ⟩₊ _ ⟨ ε ⟩₊ ⟩
            ⟨ δ ⟩₊ ℚ.+ (ℚ.- ⟨ η ⟩₊ ℚ.+ ⟨ ε ⟩₊) ≡⟨ cong (⟨ δ ⟩₊ ℚ.+_) (ℚ.+Comm _ ⟨ ε ⟩₊) ⟩
            ⟨ δ ⟩₊ ℚ.+ (ε -₊ η)               ≡⟨ ℚ.+Assoc ⟨ δ ⟩₊ _ _ ⟩
            (δ +₊ ε) -₊ η                     ∎)
          (Bx,z→By,z η [ δ -₊ η ]⟨ η<δ ⟩ B[δ-η]ιx,zη)
      in
        η , η<δ+ε , B[δ+ε-η]ιy,zη
    isPropA e z = isPropΠ λ δ → isProp→ (isPropBall (snd B⟨ι y ,⟩) (δ +₊ ε) z)

private
  B⟨ι,⟩≈ᴮB⟨ι,⟩ : (x y : M) (ε : ℚ₊) → x ≈[ ε ] y → B⟨ι x ,⟩ ≈ᴮ[ ε ] B⟨ι y ,⟩
  B⟨ι,⟩≈ᴮB⟨ι,⟩ x y ε x≈y δ z .fst = B⟨ι,⟩→B⟨ι,⟩ x y ε x≈y z δ
  B⟨ι,⟩≈ᴮB⟨ι,⟩ x y ε x≈y δ z .snd = B⟨ι,⟩→B⟨ι,⟩ y x ε (isSym≈ x y ε x≈y) z δ

module _
  (x : M) (By : ℚ₊ → Balls) (ε δ : ℚ₊)
  (Byc : ∀ α β → By α ≈ᴮ[ α +₊ β ] By β)
  (Δ : 0 <ℚ ε -₊ δ)
  (Bιx≈ᴮ[ε-δ]Byδ : B⟨ι x ,⟩ ≈ᴮ[ ε -₊ δ , Δ ] By δ)
  where

  open IsBall

  B⟨ι,⟩→B⟨lim,⟩ : ∀ z η → B[ η ]⟨ι x , z ⟩ → B[ η +₊ ε ]⟨limᴿ[ By , Byc ], z ⟩
  B⟨ι,⟩→B⟨lim,⟩ = Elimℭ-Prop.go e where
    open Elimℭ-Prop

    e : Elimℭ-Prop λ z → ∀ η → B[ η ]⟨ι x , z ⟩ → B[ η +₊ ε ]⟨limᴿ[ By , Byc ], z ⟩
    ιA      e z η (lift x≈z) =
      let
        δ<η+ε : δ <₊ (η +₊ ε)
        δ<η+ε = begin<
          ⟨ δ ⟩₊      <⟨ 0<-→< ⟨ δ ⟩₊ ⟨ ε ⟩₊ Δ ⟩
          ⟨ ε ⟩₊      <⟨ <₊SumRight ε η ⟩
          ⟨ η +₊ ε ⟩₊ ◾

        B[η+ε-δ]yδ,ιz : fst (By δ) [ (η +₊ ε) -₊ δ ]⟨ δ<η+ε ⟩ (ι z)
        B[η+ε-δ]yδ,ιz = subst (flip (fst (By δ)) (ι z))
          (ℚ₊≡ $ ℚ.+Assoc ⟨ η ⟩₊ ⟨ ε ⟩₊ _)
          (fst (Bιx≈ᴮ[ε-δ]Byδ η (ι z)) (lift x≈z)
            :> fst (By δ) (η +₊ (ε -₊ δ , Δ)) (ι z))
      in
        ∣ δ , δ<η+ε , B[η+ε-δ]yδ,ιz ∣₁
    limA    e z zc Bx,z→Blimy,z η = PT.map λ (θ , θ<η , B[η-θ]x,zθ) →
      let
        δ+θ<η+ε : (δ +₊ θ) <₊ (η +₊ ε)
        δ+θ<η+ε = begin<
          ⟨ δ +₊ θ ⟩₊ ≡→≤⟨ ℚ.+Comm ⟨ δ ⟩₊ ⟨ θ ⟩₊ ⟩
          ⟨ θ +₊ δ ⟩₊   <⟨ +Mono< ⟨ θ ⟩₊ _ ⟨ δ ⟩₊ _ θ<η (0<-→< ⟨ δ ⟩₊ ⟨ ε ⟩₊ Δ) ⟩
          ⟨ η +₊ ε ⟩₊   ◾

        B[η-θ+ε-δ]yδ,zθ : fst (By δ) ([ η -₊ θ ]⟨ θ<η ⟩ +₊ (ε -₊ δ , Δ)) (z θ)
        B[η-θ+ε-δ]yδ,zθ = fst (Bιx≈ᴮ[ε-δ]Byδ [ η -₊ θ ]⟨ θ<η ⟩ (z θ)) B[η-θ]x,zθ

        B[η+ε-[δ+θ]]yδ,zθ : fst (By δ) [ (η +₊ ε) -₊ (δ +₊ θ) ]⟨ δ+θ<η+ε ⟩ (z θ)
        B[η+ε-[δ+θ]]yδ,zθ = flip (subst (flip (fst (By δ)) (z θ))) B[η-θ+ε-δ]yδ,zθ $
          ℚ₊≡ $
          (η -₊ θ) ℚ.+ (ε -₊ δ)                    ≡⟨ +ShufflePairs ⟨ η ⟩₊ _ ⟨ ε ⟩₊ _ ⟩
          ⟨ η +₊ ε ⟩₊ ℚ.+ ((ℚ.- ⟨ θ ⟩₊) ℚ.- ⟨ δ ⟩₊) ≡⟨ cong (⟨ η +₊ ε ⟩₊ ℚ.+_)
                                                           (-Dist ⟨ θ ⟩₊ _) ⟩
          ⟨ η +₊ ε ⟩₊ ℚ.- ⟨ θ +₊ δ ⟩₊               ≡⟨ cong (ℚ._-_ ⟨ η +₊ ε ⟩₊)
                                                           (ℚ.+Comm ⟨ θ ⟩₊ ⟨ δ ⟩₊) ⟩
          (η +₊ ε) -₊ (δ +₊ θ)                     ∎

      in
        δ , θ , δ+θ<η+ε , B[η+ε-[δ+θ]]yδ,zθ
    isPropA e z = isPropΠ λ η → isProp→ (isPropBall (snd B⟨limᴿ[ By , Byc ],⟩) (η +₊ ε) z)

  B⟨lim,⟩→B⟨ι,⟩ : ∀ z η → B[ η ]⟨limᴿ[ By , Byc ], z ⟩ → B[ η +₊ ε ]⟨ι x , z ⟩
  B⟨lim,⟩→B⟨ι,⟩ = Elimℭ-Prop.go e where
    open Elimℭ-Prop

    e : Elimℭ-Prop λ z → ∀ η → B[ η ]⟨limᴿ[ By , Byc ], z ⟩ → B[ η +₊ ε ]⟨ι x , z ⟩
    ιA      e z η = PT.rec (isPropBall (snd B⟨ι x ,⟩) (η +₊ ε) (ι z))
      λ (θ , θ<η , B[η-θ]yθ,z) →
      subst (B[_]⟨ι x , ι z ⟩)
      (ℚ₊≡ (lemma7 ℚCR ⟨ η ⟩₊ ⟨ θ ⟩₊ ⟨ δ ⟩₊ ⟨ ε ⟩₊))
      (snd (Bιx≈ᴮ[ε-δ]Byδ ([ η -₊ θ ]⟨ θ<η ⟩ +₊ (θ +₊ δ)) (ι z))
      (fst (Byc θ δ [ η -₊ θ ]⟨ θ<η ⟩ (ι z)) (
      B[η-θ]yθ,z
        :> fst (By θ) [ η -₊ θ ]⟨ θ<η ⟩ (ι z))
        :> fst (By δ) ([ η -₊ θ ]⟨ θ<η ⟩ +₊ (θ +₊ δ)) (ι z))
        :> B[ [ η -₊ θ ]⟨ θ<η ⟩ +₊ (θ +₊ δ) +₊ (ε -₊ δ , Δ) ]⟨ι x , ι z ⟩)
        :> B[ η +₊ ε ]⟨ι x , ι z ⟩
    limA    e z zc Blimy,z→Bx,z η = PT.map λ (ζ , ξ , ζ+ξ<η , B[η-[ζ+ξ]]yζ,zξ) →
      let
        ε-δ = (ε -₊ δ , Δ) ; η-[ζ+ξ] = [ η -₊ (ζ +₊ ξ) ]⟨ ζ+ξ<η ⟩

        ξ<η+ε : ξ <₊ (η +₊ ε)
        ξ<η+ε = begin<
          ⟨ ξ ⟩₊             <⟨ <₊SumRight ξ ζ ⟩
          ⟨ ζ +₊ ξ ⟩₊        <⟨ <₊SumLeft (ζ +₊ ξ) δ ⟩
          ⟨ (ζ +₊ ξ) +₊ δ ⟩₊ <⟨ +Mono< ⟨ ζ +₊ ξ ⟩₊ _ ⟨ δ ⟩₊ _ ζ+ξ<η (0<-→< ⟨ δ ⟩₊ _ Δ) ⟩
          ⟨ η +₊ ε ⟩₊        ◾

        B[η+ε-ξ]x,zξ : B[ [ (η +₊ ε) -₊ ξ ]⟨ ξ<η+ε ⟩ ]⟨ι x , z ξ ⟩
        B[η+ε-ξ]x,zξ = subst B[_]⟨ι x , z ξ ⟩
          (ℚ₊≡ (lemma8 ℚCR ⟨ η ⟩₊ ⟨ ζ ⟩₊ ⟨ ξ ⟩₊ ⟨ δ ⟩₊ ⟨ ε ⟩₊))
          (snd (Bιx≈ᴮ[ε-δ]Byδ (η-[ζ+ξ] +₊ (ζ +₊ δ)) (z ξ))
            (fst (Byc ζ δ η-[ζ+ξ] (z ξ)) (B[η-[ζ+ξ]]yζ,zξ
            :> fst (By ζ) η-[ζ+ξ] (z ξ))
            :> fst (By δ) (η-[ζ+ξ] +₊ (ζ +₊ δ)) (z ξ))
            :> B[ η-[ζ+ξ] +₊ (ζ +₊ δ) +₊ ε-δ ]⟨ι x , z ξ ⟩)

      in
        ξ , ξ<η+ε , B[η+ε-ξ]x,zξ
    isPropA e z = isPropΠ λ η → isProp→ (isPropBall (snd B⟨ι x ,⟩) (η +₊ ε) z)

  B⟨ι,⟩≈ᴮB⟨lim,⟩ : B⟨ι x ,⟩ ≈ᴮ[ ε ] B⟨limᴿ[ By , Byc ],⟩
  B⟨ι,⟩≈ᴮB⟨lim,⟩ η z .fst = B⟨ι,⟩→B⟨lim,⟩ z η
  B⟨ι,⟩≈ᴮB⟨lim,⟩ η z .snd = B⟨lim,⟩→B⟨ι,⟩ z η

module _
  (Bx By : ℚ₊ → Balls) (ε δ η : ℚ₊)
  (Bxc : ∀ α β → (Bx α) ≈ᴮ[ α +₊ β ] (Bx β))
  (Byc : ∀ α β → (By α) ≈ᴮ[ α +₊ β ] (By β))
  (Δ : 0 <ℚ (ε -₊ (δ +₊ η)))
  (Bxδ≈[ε-[δ+η]]Byη : (Bx δ) ≈ᴮ[ ε -₊ (δ +₊ η) , Δ ] (By η))
  where

  open IsBall

  B⟨lim,⟩→B⟨lim,⟩ : ∀ z θ → B[ θ ]⟨limᴿ[ Bx , Bxc ], z ⟩ → B[ θ +₊ ε ]⟨limᴿ[ By , Byc ], z ⟩
  B⟨lim,⟩→B⟨lim,⟩ = Elimℭ-Prop.go e where
    open Elimℭ-Prop

    e : Elimℭ-Prop λ z → ∀ θ → B[ θ ]⟨limᴿ[ Bx , Bxc ], z ⟩ → B[ θ +₊ ε ]⟨limᴿ[ By , Byc ], z ⟩
    ιA      e z θ = PT.map λ (ζ , ζ<θ , B[θ-ζ]xζ,z) →
      let
        ε-[δ+η] = (ε -₊ (δ +₊ η) , Δ) ; θ-ζ = [ θ -₊ ζ ]⟨ ζ<θ ⟩

        η<θ+ε : η <₊ (θ +₊ ε)
        η<θ+ε = begin<
          ⟨ η ⟩₊      <⟨ <₊SumRight η δ ⟩
          ⟨ δ +₊ η ⟩₊ <⟨ 0<-→< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ Δ ⟩
          ⟨ ε ⟩₊      <⟨ <₊SumRight ε θ ⟩
          ⟨ θ +₊ ε ⟩₊ ◾

        B[θ+ε-η]yη,z : fst (By η) [ (θ +₊ ε) -₊ η ]⟨ η<θ+ε ⟩ (ι z)
        B[θ+ε-η]yη,z = subst (flip (fst (By η)) (ι z))
          (ℚ₊≡ (lemma9 ℚCR ⟨ θ ⟩₊ ⟨ ζ ⟩₊ ⟨ δ ⟩₊ ⟨ ε ⟩₊ ⟨ η ⟩₊))
          (fst (Bxδ≈[ε-[δ+η]]Byη (θ-ζ +₊ (ζ +₊ δ)) (ι z))
          (fst (Bxc ζ δ θ-ζ (ι z)) (B[θ-ζ]xζ,z
            :> fst (Bx ζ) θ-ζ (ι z))
            :> fst (Bx δ) (θ-ζ +₊ (ζ +₊ δ)) (ι z))
            :> fst (By η) (θ-ζ +₊ (ζ +₊ δ) +₊ ε-[δ+η]) (ι z))

      in
        η , η<θ+ε , B[θ+ε-η]yη,z
    limA    e z zc _ θ = PT.map λ (ζ , ξ , ζ+ξ<θ , B[θ-[ζ+ξ]]xζ,zξ) →
      let
        ε-[δ+η] = (ε -₊ (δ +₊ η) , Δ) ; θ-[ζ+ξ] = [ θ -₊ (ζ +₊ ξ) ]⟨ ζ+ξ<θ ⟩

        η+ξ<θ+ε : (η +₊ ξ) <₊ (θ +₊ ε)
        η+ξ<θ+ε = begin<
          ⟨ η +₊ ξ ⟩₊                 <⟨ +Mono< ⟨ η ⟩₊ _ ⟨ ξ ⟩₊ _
                                        (<₊SumRight η δ) (<₊SumRight ξ ζ) ⟩
          ⟨ (δ +₊ η) +₊ (ζ +₊ ξ) ⟩₊   <⟨ +Mono< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ ⟨ ζ +₊ ξ ⟩₊ ⟨ θ ⟩₊
                                        (0<-→< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ Δ) ζ+ξ<θ ⟩
          ⟨ ε +₊ θ ⟩₊               ≡→≤⟨ ℚ.+Comm ⟨ ε ⟩₊ ⟨ θ ⟩₊ ⟩
          ⟨ θ +₊ ε ⟩₊                 ◾

        B[θ+ε-[η+ξ]]yη,zξ : fst (By η) [ (θ +₊ ε) -₊ (η +₊ ξ) ]⟨ η+ξ<θ+ε ⟩ (z ξ)
        B[θ+ε-[η+ξ]]yη,zξ = subst (flip (fst (By η)) (z ξ))
          (ℚ₊≡ (lemma10 ℚCR ⟨ θ ⟩₊ ⟨ ζ ⟩₊ ⟨ ξ ⟩₊ ⟨ δ ⟩₊ ⟨ ε ⟩₊ ⟨ η ⟩₊))
          (fst (Bxδ≈[ε-[δ+η]]Byη (θ-[ζ+ξ] +₊ (ζ +₊ δ)) (z ξ))
            (fst (Bxc ζ δ θ-[ζ+ξ] (z ξ)) (B[θ-[ζ+ξ]]xζ,zξ
            :> fst (Bx ζ) θ-[ζ+ξ] (z ξ))
            :> fst (Bx δ) (θ-[ζ+ξ] +₊ (ζ +₊ δ)) (z ξ))
            :> fst (By η) (θ-[ζ+ξ] +₊ (ζ +₊ δ) +₊ ε-[δ+η]) (z ξ))

      in
        η , ξ , η+ξ<θ+ε , B[θ+ε-[η+ξ]]yη,zξ
    isPropA e z = isPropΠ λ θ → isProp→ (isPropBall (snd B⟨limᴿ[ By , Byc ],⟩) (θ +₊ ε) z)

private
  B⟨lim,⟩≈B⟨lim,⟩ : ∀ Bx By ε δ η Bxc Byc Δ
                   → (Bx δ) ≈ᴮ[ ε -₊ (δ +₊ η) , Δ ] (By η)
                   → B⟨limᴿ[ Bx , Bxc ],⟩ ≈ᴮ[ ε ] B⟨limᴿ[ By , Byc ],⟩
  B⟨lim,⟩≈B⟨lim,⟩ Bx By ε δ η Bxc Byc Δ Bxδ≈[ε-[δ+η]]Byη θ z .fst =
    B⟨lim,⟩→B⟨lim,⟩ Bx By ε δ η Bxc Byc Δ Bxδ≈[ε-[δ+η]]Byη z θ
  B⟨lim,⟩≈B⟨lim,⟩ Bx By ε δ η Bxc Byc Δ Bxδ≈[ε-[δ+η]]Byη θ z .snd =
    B⟨lim,⟩→B⟨lim,⟩ By Bx ε η δ Byc Bxc Δ' Byη≈[ε-[η+δ]]Bxδ z θ
    where
      p : ε -₊ (η +₊ δ) ≡ ε -₊ (δ +₊ η)
      p = cong (ℚ._-_ ⟨ ε ⟩₊) (ℚ.+Comm ⟨ η ⟩₊ ⟨ δ ⟩₊)

      Δ' : 0 <ℚ ε -₊ (η +₊ δ)
      Δ' = ≡₊→0< (ε -₊ (δ +₊ η) , Δ) (cong (ℚ._-_ ⟨ ε ⟩₊) (ℚ.+Comm ⟨ η ⟩₊ ⟨ δ ⟩₊))

      Byη≈[ε-[η+δ]]Bxδ : (By η) ≈ᴮ[ ε -₊ (η +₊ δ) , Δ' ] (Bx δ)
      Byη≈[ε-[η+δ]]Bxδ = subst ((By η) ≈ᴮ[_] (Bx δ)) (ℚ₊≡ (sym p))
        (isSym≈ᴮ (Bx δ) (By η) (ε -₊ (δ +₊ η) , Δ) Bxδ≈[ε-[δ+η]]Byη)


BallsAt[Rec] : RecℭSym Balls (flip ∘ _≈ᴮ[_]_)
ιA        BallsAt[Rec] = B⟨ι_,⟩
limA      BallsAt[Rec] = B⟨limᴿ[_,_],⟩
eqA       BallsAt[Rec] = isSeparated≈ᴮ
ι-ι-B     BallsAt[Rec] = B⟨ι,⟩≈ᴮB⟨ι,⟩
ι-lim-B   BallsAt[Rec] = B⟨ι,⟩≈ᴮB⟨lim,⟩
lim-lim-B BallsAt[Rec] = B⟨lim,⟩≈B⟨lim,⟩
isSymB    BallsAt[Rec] = isSym≈ᴮ
isPropB   BallsAt[Rec] = isProp≈ᴮ

-- Defintion 3.13 (second part)
B⟨_,⟩ : ℭM → Balls
B⟨_,⟩ = RecℭSym.go BallsAt[Rec]

B[_]⟨_,_⟩ : ℚ₊ → ℭM → ℭM → Type (ℓ-max ℓ ℓ')
B[_]⟨_,_⟩ = flip (fst ∘ B⟨_,⟩)

isNonExpanding∼→≈ᴮB⟨,⟩ : nonExpanding∼→≈ᴮ B⟨_,⟩
isNonExpanding∼→≈ᴮB⟨,⟩ = λ _ _ _ → RecℭSym.go∼ BallsAt[Rec]

-- Theorem 3.14
module _ where
  _ : ∀ {ε x y} → B[ ε ]⟨ ι x , ι y ⟩ ≡ Lift {ℓ'} {ℓ} (x ≈[ ε ] y)
  _ = refl

  _ : ∀ {ε x y yc}
      → B[ ε ]⟨ ι x , lim y yc ⟩
      ≡ (∃[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ] B[ [ ε -₊ δ ]⟨ δ<ε ⟩ ]⟨ ι x , y δ ⟩)
  _ = refl

  _ : ∀ {ε x y xc}
      → B[ ε ]⟨ lim x xc , ι y ⟩
      ≡ (∃[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ] B[ [ ε -₊ δ ]⟨ δ<ε ⟩ ]⟨ x δ , ι y ⟩)
  _ = refl

  _ : ∀ {ε x y xc yc}
      → B[ ε ]⟨ lim x xc , lim y yc ⟩
      ≡ (∃[ δ ∈ ℚ₊ ] Σ[ η ∈ ℚ₊ ] Σ[ δ+η<ε ∈ ((δ +₊ η) <₊ ε) ]
          B[ [ ε -₊ (δ +₊ η) ]⟨ δ+η<ε ⟩ ]⟨ x δ , y η ⟩)
  _ = refl

  -- With the other approach (see the commented code at the end of the file),
  -- we would get only this computation rule, instead of the two above:
  -- _ : ∀ {ε x y xc yc}
  --     → B[ ε ]⟨ lim x xc , lim y yc ⟩
  --     ≡ (∃[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ] B[ [ ε -₊ δ ]⟨ δ<ε ⟩ ]⟨ x δ , lim y yc ⟩)
  -- _ = refl

{-
∼→B : ∀ {x y ε} → x ∼[ ε ] y → B[ ε ]⟨ x , y ⟩
∼→B = Recℭ∼.go∼ r where
  r : Recℭ∼ λ x y → B[_]⟨ x , y ⟩
  Recℭ∼.ι-ι-B     r x y ε = lift
  Recℭ∼.ι-lim-B   r x y ε δ yc Δ _ q      =
    ∣ δ , 0<-→< ⟨ δ ⟩₊ ⟨ ε ⟩₊ Δ , subst B[_]⟨ ι x , y δ ⟩ (ℚ₊≡ refl) q ∣₁
  Recℭ∼.lim-ι-B   r x y ε δ xc Δ _ q      =
    ∣ δ , 0<-→< ⟨ δ ⟩₊ ⟨ ε ⟩₊ Δ , subst B[_]⟨ x δ , ι y ⟩ (ℚ₊≡ refl) q ∣₁
  Recℭ∼.lim-lim-B r x y ε δ η xc yc Δ _ q =
    ∣ δ , η , 0<-→< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ Δ , subst B[_]⟨ x δ , y η ⟩ (ℚ₊≡ refl) q ∣₁
  Recℭ∼.isPropB   r x y ε                 = IsBall.isPropBall (snd B⟨ x ,⟩) ε y

B→∼ : ∀ {x y ε} → B[ ε ]⟨ x , y ⟩ → x ∼[ ε ] y
B→∼ = {!   !}

-- Theorem 3.15
∼≃B : ∀ {x y ε} → (x ∼[ ε ] y) ≃ B[ ε ]⟨ x , y ⟩
∼≃B {x} {y} {ε} =
  propBiimpl→Equiv (isProp∼ x ε y) (IsBall.isPropBall (snd B⟨ x ,⟩) ε y) ∼→B B→∼

-- -}

-- This is the wrong approach (see the computations in Theorem 3.14)
-- BallsAt[Rec] : Recℭ Balls (flip ∘ _≈ᴮ[_]_)
-- BallsAt[Rec] .ιA          = B⟨ι_,⟩
-- BallsAt[Rec] .limA Bx Bxc .fst = λ ε y →
--   ∃[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ _ ] fst (Bx δ) [ ε -₊ δ ]⟨ δ<ε ⟩ y
-- BallsAt[Rec] .limA Bx Bxc .snd = isB where
--   open IsBall
--   open Elimℭ-Prop
--   module Bx (η : ℚ₊) = IsBall (snd (Bx η))
--
--   isB : IsBall _
--   isB .isPropBall       = λ _ _ → squash₁
--   isB .isRoundedBall    = λ ε y → PT.rec squash₁
--     λ (δ , δ<ε , B[ε-δ]x,yδ) →
--     flip PT.map (Bx.isRoundedBall δ [ ε -₊ δ ]⟨ δ<ε ⟩ y B[ε-δ]x,yδ)
--       λ (ξ , ξ<ε-δ , B[ξ]x,yδ) →
--       let
--
--         δ<ξ+δ : δ <₊ (ξ +₊ δ)
--         δ<ξ+δ = <₊SumRight δ ξ
--
--         ξ+δ<ε : (ξ +₊ δ) <₊ ε
--         ξ+δ<ε = begin<
--           ⟨ ξ +₊ δ ⟩₊         <⟨ ℚ.<-+o ⟨ ξ ⟩₊ (ε -₊ δ) ⟨ δ ⟩₊ ξ<ε-δ ⟩
--           ε -₊ δ ℚ.+ ⟨ δ ⟩₊ ≡→≤⟨ minusPlus₊ ε δ ⟩
--           ⟨ ε ⟩₊              ◾
--
--         B[ξ+δ-δ]x,y : fst (Bx δ) [ (ξ +₊ δ) -₊ δ ]⟨ δ<ξ+δ ⟩ y
--         B[ξ+δ-δ]x,y = subst (flip (fst (Bx δ)) y) (ℚ₊≡ (sym (plusMinus₊ ξ δ))) B[ξ]x,yδ
--
--       in
--         ξ +₊ δ , ξ+δ<ε , ∣ δ , δ<ξ+δ , B[ξ+δ-δ]x,y ∣₁
--   isB .isTriangularBall = λ ε δ y z → flip λ y∼z → PT.map λ (η , η<ε , B[ε-η]xη,y) →
--     let
--       η<ε+δ : η <₊ (ε +₊ δ)
--       η<ε+δ = begin<
--         ⟨ η ⟩₊      <⟨ η<ε ⟩
--         ⟨ ε ⟩₊      <⟨ <₊SumLeft ε δ ⟩
--         ⟨ ε +₊ δ ⟩₊ ◾
--
--       B[ε-η+δ]xη,z : fst (Bx η) ([ ε -₊ η ]⟨ η<ε ⟩ +₊ δ) z
--       B[ε-η+δ]xη,z = Bx.isTriangularBall η [ ε -₊ η ]⟨ η<ε ⟩ δ y z B[ε-η]xη,y y∼z
--
--       B[ε+δ-η]xη,z : fst (Bx η) [ (ε +₊ δ) -₊ η ]⟨ η<ε+δ ⟩ z
--       B[ε+δ-η]xη,z = flip (subst (flip (fst (Bx η)) z)) B[ε-η+δ]xη,z $ ℚ₊≡ $
--         (ε -₊ η) ℚ.+ ⟨ δ ⟩₊               ≡⟨ sym $ ℚ.+Assoc ⟨ ε ⟩₊ (ℚ.- ⟨ η ⟩₊) _ ⟩
--         ⟨ ε ⟩₊ ℚ.+ (ℚ.- ⟨ η ⟩₊ ℚ.+ ⟨ δ ⟩₊) ≡⟨ cong (⟨ ε ⟩₊ ℚ.+_) (ℚ.+Comm (ℚ.- ⟨ η ⟩₊) _)⟩
--         ⟨ ε ⟩₊ ℚ.+ (δ -₊ η)               ≡⟨ ℚ.+Assoc ⟨ ε ⟩₊ ⟨ δ ⟩₊ _ ⟩
--         (ε +₊ δ) -₊ η                     ∎
--     in
--       η , η<ε+δ , B[ε+δ-η]xη,z
-- BallsAt[Rec] .eqA         = isSeparated≈ᴮ
-- BallsAt[Rec] .ι-ι-B       = {!    !}
-- BallsAt[Rec] .ι-lim-B     = {!    !}
-- BallsAt[Rec] .lim-ι-B     = {!   !}
-- BallsAt[Rec] .lim-lim-B   = {!   !}
-- BallsAt[Rec] .isPropB     = isProp≈ᴮ
