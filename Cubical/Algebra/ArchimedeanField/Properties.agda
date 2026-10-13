module Cubical.Algebra.ArchimedeanField.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Algebra.ArchimedeanField.Base
open import Cubical.Algebra.ArchimedeanRing.Base
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.HeytingField.Base
open import Cubical.Algebra.HeytingField.Properties
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Morphisms
open import Cubical.Algebra.OrderedField as OF
open import Cubical.Algebra.OrderedField.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Fast.Int.Base as ℤ
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_ ; -_ to -ℤ_ ; _-_ to _-ℤ_)
import Cubical.Data.Fast.Int.Properties as ℤ
import Cubical.Data.Fast.Int.Order as ℤ
open import Cubical.Data.Rationals as ℚ
  renaming (_+_ to _+ℚ_ ; _·_ to _·ℚ_ ; -_ to -ℚ_ ; _-_ to _-ℚ_)
open import Cubical.Data.Rationals.Floor
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Rationals.Positive as ℚ
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.MagicTrick
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Poset hiding (isPseudolattice)
open import Cubical.Relation.Binary.Order.Pseudolattice

open import Cubical.Reflection.RecordEquiv

open import Cubical.Tactics.CommRingSolver

-- open PositiveRationals
-- open ℚ₊Inverse using (_⁻¹₊ ; ⁻¹inverse) renaming (_/_ to _/ℚ₊_)
{- ---- To add in the module above ↑ ----  -}

-- open import Optimizations.RationalsLogarithm.PositiveFloor

private
  variable
    ℓ ℓ' : Level

ArchimedeanField→StrictOrder : ArchimedeanField ℓ ℓ' → StrictOrder ℓ ℓ'
ArchimedeanField→StrictOrder = OrderedField→StrictOrder ∘ ArchimedeanField→OrderedField

ArchimedeanField→PseudoLattice : ArchimedeanField ℓ ℓ' → Pseudolattice ℓ ℓ'
ArchimedeanField→PseudoLattice = OrderedField→PseudoLattice ∘ ArchimedeanField→OrderedField

ArchimedeanField→Poset : ArchimedeanField ℓ ℓ' → Poset ℓ ℓ'
ArchimedeanField→Poset = OrderedField→Poset ∘ ArchimedeanField→OrderedField

ArchimedeanField→Quoset : ArchimedeanField ℓ ℓ' → Quoset ℓ ℓ'
ArchimedeanField→Quoset = OrderedField→Quoset ∘ ArchimedeanField→OrderedField

ArchimedeanField→ArchimedeanRing : ArchimedeanField ℓ ℓ' → ArchimedeanRing ℓ ℓ'
fst (ArchimedeanField→ArchimedeanRing A) = fst A
snd (ArchimedeanField→ArchimedeanRing A) = ARStr where
  module A where
    open ArchimedeanFieldStr (snd A) renaming (isHomomorphism to ιOFHom) public
    open OrderedFieldReasoning (ArchimedeanField→OrderedField A) public
    open OrderedFieldTheory (ArchimedeanField→OrderedField A) public
    open OF.Positive (ArchimedeanField→OrderedField A) 0<+Closed 0<·Closed public
  open A hiding (_·₊_ ; _⁻¹₊ ; _/₊_ ; _₊/₊_ ; ⟨_⟩₊)
  module AR = ArchimedeanRingStr renaming (isArchimedeanRing to isAR)

  ARStr : ArchimedeanRingStr _ (fst A)
  AR.0r  ARStr = 0f
  AR.1r  ARStr = 1f
  AR._+_ ARStr = _+_
  AR._·_ ARStr = _·_
  AR.-_  ARStr = -_
  AR._<_ ARStr = _<_
  AR._≤_ ARStr = _≤_
  AR.ι   ARStr = ι ∘ [_/ 1 ]
  AR.isAR ARStr .IsArchimedeanRing.isOrderedCommRing   = isOrderedCommRing
  AR.isAR ARStr .IsArchimedeanRing.·CancelR<           = ·CancelR<
  AR.isAR ARStr .IsArchimedeanRing.isMonomorphism      = snd ((_ , ιOFHom) ∘ocr↪ ℤ↪ℚOCR)
  AR.isAR ARStr .IsArchimedeanRing.archimedeanProperty = λ x y 0<y → do
    (inl 0<x) ← is-weakly-linear 0f y x 0<y
      where
      (inr x<y) → return (1 , subst (x <_) (sym (congL _·_ ιpres1 ∙ A.·IdL y)) x<y)
    let
      x₊ = x , 0<x ; y₊ = y , 0<y ; y/x = y A./₊ x₊
    (q , 0<q , q<y/x) ← uncurry (archimedeanProperty 0f) (y₊ A.₊/₊ x₊)
    let
      q₊ = q , recompute< (ιreflect< 0 q (subst (_< ι q) (sym ιpres0) 0<q))
      ι₊ = ι ∘ ⟨_⟩₊
      0<ι₊ = subst (_< ι _) ιpres0 ∘ uncurry (ιpres< 0)

      x≡ι⌈1/q⌉·ιq·x : x ≡ ι₊ (q₊ ⁻¹₊) · (ι q · x)
      x≡ι⌈1/q⌉·ιq·x =
        x                       ≡⟨ sym $ congL _·_ ιpres1 ∙ A.·IdL x ⟩
        ι 1 · x                 ≡⟨ sym $ congL _·_ $ cong ι $ ℚ.·₊-linv q₊ ⟩
        ι₊ (q₊ ⁻¹₊ ·₊ q₊) · x   ≡⟨ congL _·_ (ιpres· _ _) ∙ sym (A.·Assoc _ _ x) ⟩
        ι₊ (q₊ ⁻¹₊) · (ι q · x) ∎

      x<ι⌈1/q⌉y : x < ι ⟨ ceil₊ (q₊ ⁻¹₊) ⟩₊ · y
      x<ι⌈1/q⌉y = begin<
        x                       ≡→≤⟨ x≡ι⌈1/q⌉·ιq·x ⟩
        ι₊ (q₊ ⁻¹₊) · (ι q · x)   <⟨ [ _ , 0<ι₊ (q₊ ⁻¹₊) ]·< (q<y/x <·[ x , 0<x ]) ⟩
        ι₊ (q₊ ⁻¹₊) · (y/x · x) ≡→≤⟨ congR _·_ (A./₊· y x₊) ⟩
        ι₊ (q₊ ⁻¹₊) · y           ≤⟨ ιpres≤ _ _ (≤⌈⌉ _) ≤·[ _ , <-≤-weaken _ _ 0<y ] ⟩
        ι₊ (ceil₊ (q₊ ⁻¹₊)) · y  ◾

    return (ceil₊ℤ (q₊ ⁻¹₊) , x<ι⌈1/q⌉y)
