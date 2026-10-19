module Cubical.Algebra.ArchimedeanField.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Algebra.ArchimedeanField.Base
open import Cubical.Algebra.ArchimedeanRing
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
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
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

module _ (A' : ArchimedeanField ℓ ℓ') where
  private
    A    = fst A'
    AOF  = ArchimedeanField→OrderedField A'
    AOCR = ArchimedeanField→OrderedCommRing A'
    ACR  = ArchimedeanField→CommRing A'

  open ArchimedeanFieldStr (snd A')
  open Exponentiation ACR

  module ArchimedeanFieldReasoning where
    open OrderedFieldReasoning AOF public

    _<·ι[_] : ∀ {x y} z → x < y → x · ι₊ z < y · ι₊ z
    _<·ι[_] z = _<·[ _ , subst (_< _) ιpres0 (ιpres< _ _ (snd z)) ]

    ι[_]·<_ : ∀ {x y} z → x < y → ι₊ z · x < ι₊ z · y
    ι[_]·<_ z = [ _ , subst (_< _) ιpres0 (ιpres< _ _ (snd z)) ]·<_

    _≤·ι[_] : ∀ {x y} z → x ≤ y → x · ι₀₊ z ≤ y · ι₀₊ z
    _≤·ι[_] z = _≤·[ _ , subst (_≤ _) ιpres0 (ιpres≤ _ _ (snd z)) ]

    ι[_]·≤_ : ∀ {x y} z → x ≤ y → ι₀₊ z · x ≤ ι₀₊ z · y
    ι[_]·≤_ z = [ _ , subst (_≤ _) ιpres0 (ιpres≤ _ _ (snd z)) ]·≤_

  open ArchimedeanFieldReasoning

  module ArchimedeanFieldTheory where
    open OrderedFieldTheory AOF public

    ι0· : ∀ x → ι 0 · x ≡ 0f
    ι0· x = congL _·_ ιpres0 ∙ 0LeftAnnihilates x

    ι1· : ∀ x → ι 1 · x ≡ x
    ι1· x = congL _·_ ιpres1 ∙ ·IdL x

    0<ι₊ : ∀ a → 0f < ι₊ a
    0<ι₊ = subst (_< ι _) ιpres0 ∘ uncurry (ιpres< 0)

    0≤ι₊ : ∀ a → 0f ≤ ι₊ a
    0≤ι₊ = <-≤-weaken 0f _ ∘ 0<ι₊

    0≤ι₀₊ : ∀ a → 0f ≤ ι₀₊ a
    0≤ι₀₊ = subst (_≤ ι _) ιpres0 ∘ uncurry (ιpres≤ 0)

    archimedeanPropertyℤ : ∀ x y → 0f < y → ∃[ k ∈ ℤ ] (x < ι [ k , 1 ] · y)
    archimedeanPropertyℤ x y 0<y = do
      (inl 0<x) ← is-weakly-linear 0f y x 0<y
        where (inr x<y) → return (1 , subst (x <_) (sym (ι1· y)) x<y)
      let
        x₊ = x , 0<x ; y₊ = y , 0<y ; y/x = y A./₊ x₊
      (q , 0<ιq , q<y/x) ← uncurry (archimedeanProperty 0f) (y₊ A.₊/₊ x₊)
      let
        q₊ = q , recompute< (ιreflect< 0 q (subst (_< ι q) (sym ιpres0) 0<ιq))

        x≡ι⌈1/q⌉·ιq·x : x ≡ ι₊ (q₊ ⁻¹₊) · (ι q · x)
        x≡ι⌈1/q⌉·ιq·x =
          x                       ≡⟨ sym $ congL _·_ ιpres1 ∙ ·IdL x ⟩
          ι 1 · x                 ≡⟨ sym $ congL _·_ $ cong ι $ ℚ.·₊-linv q₊ ⟩
          ι₊ (q₊ ⁻¹₊ ·₊ q₊) · x   ≡⟨ congL _·_ (ιpres· _ _) ∙ sym (·Assoc _ _ x) ⟩
          ι₊ (q₊ ⁻¹₊) · (ι q · x) ∎

        x<ι⌈1/q⌉y : x < ι ⟨ ceil₊ (q₊ ⁻¹₊) ⟩₊ · y
        x<ι⌈1/q⌉y = begin<
          x                       ≡→≤⟨ x≡ι⌈1/q⌉·ιq·x ⟩
          ι₊ (q₊ ⁻¹₊) · (ι q · x)   <⟨ [ _ , 0<ι₊ (q₊ ⁻¹₊) ]·< (q<y/x <·[ x , 0<x ]) ⟩
          ι₊ (q₊ ⁻¹₊) · (y/x · x) ≡→≤⟨ congR _·_ (A./₊· y x₊) ⟩
          ι₊ (q₊ ⁻¹₊) · y           ≤⟨ ιpres≤ _ _ (≤⌈⌉ _) ≤·[ _ , <-≤-weaken _ _ 0<y ] ⟩
          ι₊ (ceil₊ (q₊ ⁻¹₊)) · y  ◾

      return (ceil₊ℤ (q₊ ⁻¹₊) , x<ι⌈1/q⌉y)
      where module A = OF.Positive AOF 0<+Closed 0<·Closed

  open ArchimedeanFieldTheory

  ArchimedeanField→ArchimedeanRing : ArchimedeanRing ℓ ℓ'
  fst ArchimedeanField→ArchimedeanRing = fst A'
  snd ArchimedeanField→ArchimedeanRing = ARStr where
    module AR = ArchimedeanRingStr renaming (isArchimedeanRing to isAR)
    module IsAR = IsArchimedeanRing

    ARStr : ArchimedeanRingStr ℓ' _
    AR.0r   ARStr = 0f
    AR.1r   ARStr = 1f
    AR._+_  ARStr = _+_
    AR._·_  ARStr = _·_
    AR.-_   ARStr = -_
    AR._<_  ARStr = _<_
    AR._≤_  ARStr = _≤_
    AR.ι    ARStr = ι ∘ [_/ 1 ]
    AR.isAR ARStr .IsAR.isOrderedCommRing   = isOrderedCommRing
    AR.isAR ARStr .IsAR.·CancelR<           = ·CancelR<
    AR.isAR ARStr .IsAR.isMonomorphism      = snd ((_ , isHomomorphism) ∘ocr↪ ℤ↪ℚOCR)
    AR.isAR ARStr .IsAR.archimedeanProperty = archimedeanPropertyℤ

  private
    AR = ArchimedeanField→ArchimedeanRing

  module ∃Log₊ where
    private
      module A  = OF.Positive AOF 0<+Closed 0<·Closed
      module AR where
        open ArchimedeanRingStr (snd AR) public
        open ArchimedeanRingTheory AR public
      module B≤ = BernoulliIneq AR

    1<base→∃N[<baseᴺ] : ∀ x → ∀ b → 1f < b → ∃[ N ∈ ℕ ] A.⟨ x ⟩₊ < b ^ N
    1<base→∃N[<baseᴺ] (x , 0<x) b 1<b = do
      (inl 1<x) ← is-weakly-linear 1f b x 1<b
        where (inr x<b) → return (1 , subst (x <_) (sym (·IdR _)) x<b)
      let 0≤x-1 = <-≤-weaken _ _ (<→0<Δ 1f x 1<x)
      (1+ N-1 , x-1<ιN[b-1]) ← AR.archimedeanPropertyℕ₊₁ (x - 1f) _ 0≤x-1 (<→0<Δ _ _ 1<b)
      let
        N = suc N-1
        x<bᴺ : x < b ^ N
        x<bᴺ = begin<
          x                        ≡→≤⟨ solve! ACR ⟩
          1f + (x - 1f)              <⟨ [ 1f ]+< x-1<ιN[b-1] ⟩
          1f + AR.ι₀₊ N · (b - 1f)   ≤⟨ B≤.0≤ _ (begin≤ 0f <⟨ 0<1 ⟩ 1f <⟨ 1<b ⟩ b ◾) N ⟩
          b ^ N                      ◾
      return (N , x<bᴺ)

    base∈[0,1]→∃N[baseᴺ<] : ∀ x → ∀ b → 0f < b → b < 1f → ∃[ N ∈ ℕ ] b ^ N < A.⟨ x ⟩₊
    base∈[0,1]→∃N[baseᴺ<] x₊@(x , 0<x) b 0<b b<1 = do
      (N , x⁻¹<b⁻¹ᴺ) ← 1<base→∃N[<baseᴺ] (x₊ A.⁻¹₊) _ (A.<₊1→1<₊⁻¹ (b , 0<b) b<1)
      return
        (N , A.⁻¹Flip<₊' ((b , 0<b) A.₊^ N) x₊ (subst (_ <_) (A.₊^-⁻¹₊ _ N) x⁻¹<b⁻¹ᴺ))
