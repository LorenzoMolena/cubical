{-# OPTIONS --safe #-}

module HeytingField.Subfield where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Algebra.CommRing
open import Cubical.Relation.Binary.Order.Apartness

open import HeytingField.Base
open import HeytingField.Properties

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level

module _ (F : HeytingField ℓ ℓ') where
  private module F = FieldTheory F

  record isSubfield (S : ⟨ F ⟩ → Type ℓ'') : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
    constructor makeIsSubfield
    field
      is-prop-valued : ∀ x → isProp (S x)
      0Closed : S F.0r
      +Closed : ∀ x y → S x → S y → S (x F.+ y)
      -Closed : ∀ x → S x → S (F.- x)
      1Closed : S F.1r
      ·Closed : ∀ x y → S x → S y → S (x F.· y)
      recipClosed : ∀ x x#0 → S x → S (F.recip x x#0)

  Subfield : ∀ ℓ'' → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ''))
  Subfield ℓ'' = Σ[ S ∈ (⟨ F ⟩ → Type ℓ'') ] isSubfield S

  open HeytingFieldStr
  open IsHeytingField

  getSubfield : Subfield ℓ'' → HeytingField (ℓ-max ℓ ℓ'') ℓ'
  getSubfield (S , Ss) = HF , λ where
    .0r → F.0r , Ss.0Closed
    .1r → F.1r , Ss.1Closed
    ._+_ (x , Sx) (y , Sy) → (x F.+ y) , Ss.+Closed x y Sx Sy
    ._·_ (x , Sx) (y , Sy) → (x F.· y) , Ss.·Closed x y Sx Sy
    .-_ (x , Sx) → (F.- x) , Ss.-Closed x Sx
    ._#_ (x , Sx) (y , Sy) → x F.# y
    .isHeytingField .isCommRing → 
      makeIsCommRing (isSetΣSndProp F.is-set (Ss.is-prop-valued)) 
        (λ _ _ _ → HF≡ (F.+Assoc _ _ _)) (λ _ → HF≡ (F.+IdR _)) (λ _ → HF≡ (F.+InvR _))          (λ _ _ → HF≡ (F.+Comm _ _))
        (λ _ _ _ → HF≡ (F.·Assoc _ _ _)) (λ _ → HF≡ (F.·IdR _)) (λ _ _ _ → HF≡ (F.·DistR+ _ _ _)) λ _ _ → HF≡ (F.·Comm _ _)
    .isHeytingField .isApartness → isApartnessInduced F.isApartness HF (EmbeddingΣProp Ss.is-prop-valued)
    .isHeytingField .isTight x y ¬x#y → HF≡ (F.isTight _ _ ¬x#y)
    .isHeytingField .+Respect#ᵣ x y z → F.+Respect#ᵣ _ _ _
    .isHeytingField .#0→IsInv (x , Sx) x#0 .fst → F.recip x x#0 , Ss.recipClosed x x#0 Sx
    .isHeytingField .#0→IsInv _ x#0 .snd → HF≡ (F.isRInvRecip _ x#0)
    .isHeytingField .IsInv→#0 _ _ xy≡1 → F.IsInv→#0 _ _ (cong fst xy≡1)
      where
        module Ss = isSubfield Ss
        HF = Σ[ x ∈ ⟨ F ⟩ ] S x
        HF≡ : {x y : HF} → x .fst ≡ y .fst → x ≡ y
        HF≡ = Σ≡Prop (Ss.is-prop-valued)

  getSubfieldEmb : (S : Subfield ℓ'') → HeytingFieldHom (getSubfield S) F
  getSubfieldEmb (S , Ss) = makeFieldHom fst (λ x y → refl) refl (λ x y → refl) λ x y x#y → x#y

  Subfield' : ∀ ℓ'' → Type (ℓ-max (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-suc ℓ''))
  Subfield' ℓ'' = Σ[ H ∈ HeytingField ℓ'' ℓ' ] HeytingFieldHom H F

  Subfield→Subfield' : Subfield ℓ'' → Subfield' (ℓ-max ℓ ℓ'')
  Subfield→Subfield' S = getSubfield S , getSubfieldEmb S

module _ {F : HeytingField ℓ ℓ'} where

  private module F = FieldTheory F

  isSubfieldWholeSet : isSubfield F λ _ → Unit* {ℓ''}
  isSubfieldWholeSet = makeIsSubfield (λ _ → isPropUnit*) _ (λ _ _ _ _ → _) (λ _ _ → _) _ (λ _ _ _ _ → _) (λ _ _ _ → _)

  improperSubfield : Subfield F ℓ''
  improperSubfield = _ , isSubfieldWholeSet

  isSubfieldIntersection : {A : Type ℓ'''} {P : A → ⟨ F ⟩ → Type ℓ''} 
                         → ((a : A) → isSubfield F (P a)) → isSubfield F λ x → ∀ a → P a x
  isSubfieldIntersection P = λ where
    .is-prop-valued x → isPropΠ λ a → P.is-prop-valued a x
    .0Closed a → P.0Closed a
    .+Closed x y Px Py a → P.+Closed a x y (Px a) (Py a)
    .-Closed x Px a → P.-Closed a x (Px a)
    .1Closed a → P.1Closed a
    .·Closed x y Px Py a → P.·Closed a x y (Px a) (Py a)
    .recipClosed x x#0 Px a → P.recipClosed a x x#0 (Px a)
      where
        open isSubfield
        module P (a : _) where open isSubfield (P a) public

  intersectionSubfield : {A : Type ℓ'''} → (A → Subfield F ℓ'') → Subfield F (ℓ-max ℓ''' ℓ'')
  intersectionSubfield P = _ , isSubfieldIntersection λ a → P a .snd
