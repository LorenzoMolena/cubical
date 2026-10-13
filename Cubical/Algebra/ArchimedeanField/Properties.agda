module Cubical.Algebra.ArchimedeanField.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Algebra.ArchimedeanField.Base
open import Cubical.Algebra.ArchimedeanRing.Base
-- open import Cubical.Algebra.ArchimedeanRing.Instances.Rationals
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
  -- module A where
  open module AF = ArchimedeanFieldStr (snd A) renaming (isHomomorphism to ιOFHom)

  module A where
    open OrderedFieldTheory (ArchimedeanField→OrderedField A) public
    open OF.Positive (ArchimedeanField→OrderedField A) 0<+Closed 0<·Closed public
  -- open A hiding (·CancelR<)
  module AR = ArchimedeanRingStr
  -- open IsArchimedeanRing

  ARStr : ArchimedeanRingStr _ (fst A)
  AR.0r  ARStr = 0f
  AR.1r  ARStr = 1f
  AR._+_ ARStr = _+_
  AR._·_ ARStr = _·_
  AR.-_  ARStr = -_
  AR._<_ ARStr = _<_
  AR._≤_ ARStr = _≤_
  AR.ι   ARStr = ι ∘ [_/ 1 ]
  AR.isArchimedeanRing ARStr .isOrderedCommRing   = AF.isOrderedCommRing
  AR.isArchimedeanRing ARStr .·CancelR<           = A.·CancelR<
  AR.isArchimedeanRing ARStr .isMonomorphism      = snd ((_ , ιOFHom) ∘ocr↪ ℤ↪ℚOCR)
  AR.isArchimedeanRing ARStr .archimedeanProperty = λ x y 0<y →
    do
      (inl 0<x) ← AF.is-weakly-linear 0f y x 0<y
        where
        (inr x<y) →
          return
            ( 1
            , (subst (x <_) (sym (congL _·_ ιpres1 ∙ AF.·IdL y)) x<y
              :> x < ι 1 · y))
      let
        x₊ = x , 0<x ; y₊ = y , 0<y ; y/x = y A./₊ x₊
      (q , 0<q , q<y/x) ← uncurry (AF.archimedeanProperty 0f) (y₊ A.₊/₊ x₊)
      let
        q₊ = q , recompute< (ιreflect< 0 q (subst (_< ι q) (sym ιpres0) 0<q))
        1/q₊ = q₊ ⁻¹₊ ; ⌈1/q⌉ = ceil₊ 1/q₊ -- floor₊ 1/q₊

        0<ι₊ : ∀ (p : ℚ₊) → 0f < ι ⟨ p ⟩₊
        0<ι₊ p = subst (_< ι ⟨ p ⟩₊) ιpres0 (ιpres< 0 (fst p) (snd p))

        -- 0≤ι₊ : ∀ (q : ℚ₊) → 0f ≤ ι ⟨ q ⟩₊
        -- 0≤ι₊ = <-≤-weaken 0f _ ∘ 0<ι₊

        x<ι⌈1/q⌉y : x < ι ⟨ ceil₊ (q₊ ⁻¹₊) ⟩₊ · y
        x<ι⌈1/q⌉y = {!  A.begin< ? !}
      return
        (ceil₊ℤ (q₊ ⁻¹₊) ,
        {!  x<ι⌈1/q⌉y !})
    -- where open A

-- WIP
{-
ArchimedeanField→ArchimedeanRing : ArchimedeanField ℓ ℓ' → ArchimedeanRing ℓ ℓ'
fst (ArchimedeanField→ArchimedeanRing A) = fst A
snd (ArchimedeanField→ArchimedeanRing A) = ARStr where
  open module A = ArchimedeanFieldStr (snd A) renaming (isOrderedFieldHom to ιOFHom)

  ARStr : ArchimedeanRingStr _ (fst A)
  ArchimedeanRingStr.0r  ARStr = 0f
  ArchimedeanRingStr.1r  ARStr = 1f
  ArchimedeanRingStr._+_ ARStr = _+_
  ArchimedeanRingStr._·_ ARStr = _·_
  ArchimedeanRingStr.-_  ARStr = -_
  ArchimedeanRingStr._<_ ARStr = _<_
  ArchimedeanRingStr._≤_ ARStr = _≤_
  ArchimedeanRingStr.ι   ARStr = fst ((ι , ιOFHom) ∘ocr↪ ℤ↪ℚOCR)
  ArchimedeanRingStr.isArchimedeanRing ARStr = isAR where
    open OrderedFieldTheory (ArchimedeanField→OrderedField A)
      using (·CancelR< ; _[_]⁻¹ ; _/_[_] ; _/₊_ ; /₊·)
    open OrderedCommRingReasoning (ArchimedeanField→OrderedCommRing A)
    -- open IsOrderedCommRingMono A.isOrderedFieldHom

    isAR : IsArchimedeanRing _ _ _ _ _ _ _ _
    isAR .IsArchimedeanRing.isOrderedCommRing   = isOrderedCommRing
    isAR .IsArchimedeanRing.·CancelR<           = ·CancelR<
    isAR .IsArchimedeanRing.isMonomorphism      = snd ((ι , ιOFHom) ∘ocr↪ ℤ↪ℚOCR)
    isAR .IsArchimedeanRing.archimedeanProperty = λ x y 0<y →
      let y₊ = y , 0<y
      in do
        (inl 0<x) ← is-weakly-linear 0f y x 0<y
          where
          (inr x<y) →
            return (1 , (subst (x <_) (sym (cong (_· y) ιpres1 ∙ A.·IdL y)) x<y))
        let x₊ = x , 0<x ; y/x = fst (y₊ /₊ x₊)
        (q , 0<q , q<y/x) ← uncurry (archimedeanProperty 0f) (y₊ /₊ x₊)
        let
          q₊   = q , ℚ.recompute< (ιreflect< 0 q (subst (_< ι q) (sym ιpres0) 0<q))
          1/q₊ = q₊ ⁻¹₊
          ⌊1/q⌋ = floor₊ 1/q₊

          -- TO MOVE
          0<ι₊ : ∀ (q : ℚ₊) → 0f < ι ⟨ q ⟩₊
          0<ι₊ q = subst (_< ι ⟨ q ⟩₊) ιpres0 (ιpres< 0 (fst q) (snd q))

          0≤ι₊ : ∀ (q : ℚ₊) → 0f ≤ ι ⟨ q ⟩₊
          0≤ι₊ = <-≤-weaken 0f _ ∘ 0<ι₊

          x<ι[1+⌊1/q⌋]y : x < ι (ℚ.[ pos (1 ℕ.+ ⌊1/q⌋) , 1 ]) · y
          x<ι[1+⌊1/q⌋]y = begin<
            x                            ≡→≤⟨ _ ≡⟨ sym $ cong (_· x) ιpres1 ∙ A.·IdL x ⟩
            ι 1 · x                        ≡⟨ sym $ cong ((_· x) ∘ ι) (⁻¹inverse q₊) ⟩
            ι ⟨ q₊ /ℚ₊ q₊ ⟩₊ · x           ≡⟨ cong ((_· x) ∘ ι) (ℚ.·Comm q _) ⟩
            ι (⟨ q₊ ⁻¹₊ ⟩₊ ℚ.· q) · x      ≡⟨ cong (_· x) (ιpres· _ q) ⟩
            (ι ⟨ q₊ ⁻¹₊ ⟩₊ · ι q) · x      ≡⟨ sym $ A.·Assoc _ (ι q) x ⟩ refl ⟩
            ι ⟨ q₊ ⁻¹₊ ⟩₊ · (ι q · x)      <⟨ [ _ , 0<ι₊ 1/q₊ ]·< (q<y/x <·[ x , 0<x ]) ⟩
            ι ⟨ q₊ ⁻¹₊ ⟩₊ · (y/x · x)    ≡→≤⟨ cong (_ ·_) (/₊· y₊ x₊) ⟩
            ι ⟨ q₊ ⁻¹₊ ⟩₊ · y              <⟨ ιpres< _ _ (<1+floor₊ 1/q₊) <·[ y , 0<y ] ⟩
            ι [ 1 +ℤ pos ⌊1/q⌋ , 1 ] · y   ◾

        return (1 +ℤ pos ⌊1/q⌋ , x<ι[1+⌊1/q⌋]y)

-- -}
