module Cubical.Algebra.OrderedCommRing.Base where
{-
  Definition of an ordered commutative ring.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

import Cubical.Functions.Logic as L

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing.Base

open import Cubical.Relation.Nullary

open import Cubical.Tactics.CommRingSolver

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset hiding (
  isPseudolattice ; isPropIsPseudolattice)
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Binary.Order.Pseudolattice

open import Cubical.Reflection.RecordEquiv

open BinaryRelation

private
  variable
    ℓ ℓ' ℓ<≤ ℓ<≤' : Level

record IsOrderedCommRing
  {R : Type ℓ}
  (0r 1r : R )
  (_+_ _·_ : R → R → R)
  (-_ : R → R)
  (_<_ _≤_ : R → R → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor isorderedcommring
  field
    isCommRing      : IsCommRing 0r 1r _+_ _·_ -_
    isPseudolattice : IsPseudolattice _≤_
    isStrictOrder   : IsStrictOrder _<_
    <-≤-weaken      : ∀ x y → x < y → x ≤ y
    ≤≃¬>            : ∀ x y → (x ≤ y) ≃ (¬ (y < x))
    +MonoR≤         : ∀ x y z → x ≤ y → (x + z) ≤ (y + z)
    +MonoR<         : ∀ x y z → x < y → (x + z) < (y + z)
    posSum→pos∨pos  : ∀ x y → 0r < (x + y) → (0r < x) L.⊔′ (0r < y)
    <-≤-trans       : ∀ x y z → x < y → y ≤ z → x < z
    ≤-<-trans       : ∀ x y z → x ≤ y → y < z → x < z
    ·MonoR≤         : ∀ x y z → 0r ≤ z → x ≤ y → (x · z) ≤ (y · z)
    ·MonoR<         : ∀ x y z → 0r < z → x < y → (x · z) < (y · z)
    ·CancelR<       : ∀ x y z → 0r < z → (x · z) < (y · z) → x < y
    0<1             : 0r < 1r

  open IsCommRing isCommRing public
  open IsPseudolattice isPseudolattice hiding (is-set) renaming (is-prop-valued to is-prop-valued≤ ; is-trans to is-trans≤
                                                                ; isPseudolattice to is-pseudolattice
                                                                ; _∧l_ to _⊓_ ; _∨l_ to _⊔_) public
  open IsStrictOrder isStrictOrder hiding (is-set) renaming (is-prop-valued to is-prop-valued< ; is-trans to is-trans<) public

unquoteDecl IsOrderedCommRingIsoΣ = declareRecordIsoΣ IsOrderedCommRingIsoΣ (quote IsOrderedCommRing)

record OrderedCommRingStr (ℓ' : Level) (R : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor orderedcommringstr
  field
    0r 1r : R
    _+_ _·_ : R → R → R
    -_ : R → R
    _<_ _≤_ : R → R → Type ℓ'
    isOrderedCommRing : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_

  open IsOrderedCommRing isOrderedCommRing public

  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_
  infix 4 _<_ _≤_

unquoteDecl OrderedCommRingStrIsoΣ = declareRecordIsoΣ OrderedCommRingStrIsoΣ (quote OrderedCommRingStr)

OrderedCommRing : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedCommRing ℓ ℓ' = TypeWithStr ℓ (OrderedCommRingStr ℓ')

module _ {R : Type ℓ} {0r 1r : R} {_+_ _·_ : R → R → R} { -_ : R → R }
  {_<_ _≤_ : R → R → Type ℓ'}
  (is-setR : isSet R)
  (+Assoc : (x y z : R) → x + (y + z) ≡ (x + y) + z)
  (+IdR : (x : R) → x + 0r ≡ x)
  (+InvR : (x : R) → x + (- x) ≡ 0r)
  (+Comm : (x y : R) → x + y ≡ y + x)
  (·Assoc : (x y z : R) → x · (y · z) ≡ (x · y) · z)
  (·IdR : (x : R) → x · 1r ≡ x)
  (·DistR+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z))
  (·Comm : (x y : R) → x · y ≡ y · x)
  (is-prop-valued≤ : isPropValued _≤_)
  (is-refl : isRefl _≤_)
  (is-trans≤ : isTrans _≤_)
  (is-antisym : isAntisym _≤_)
  (is-meet-semipseudolattice : isMeetSemipseudolattice (poset R _≤_ (isposet is-setR is-prop-valued≤ is-refl is-trans≤ is-antisym)))
  (is-join-semipseudolattice : isJoinSemipseudolattice (poset R _≤_ (isposet is-setR is-prop-valued≤ is-refl is-trans≤ is-antisym)))
  (is-prop-valued : isPropValued _<_)
  (is-irrefl : isIrrefl _<_)
  (is-trans : isTrans _<_)
  (is-asym : isAsym _<_)
  (is-weakly-linear : isWeaklyLinear _<_)
  (<-≤-weaken : ∀ x y → x < y → x ≤ y)
  (≤≃¬> : ∀ x y → (x ≤ y) ≃ (¬ (y < x)))
  (+MonoR≤ : ∀ x y z → x ≤ y → (x + z) ≤ (y + z))
  (+MonoR< : ∀ x y z → x < y → (x + z) < (y + z))
  (posSum→pos∨pos : ∀ x y → 0r < (x + y) → 0r < x L.⊔′ 0r < y)
  (<-≤-trans : ∀ x y z → x < y → y ≤ z → x < z)
  (≤-<-trans : ∀ x y z → x ≤ y → y < z → x < z)
  (·MonoR≤ : ∀ x y z → 0r ≤ z → x ≤ y → (x · z) ≤ (y · z))
  (·MonoR< : ∀ x y z → 0r < z → x < y → (x · z) < (y · z))
  (·CancelR< : ∀ x y z → 0r < z → (x · z) < (y · z) → x < y)
  (0<1 : 0r < 1r) where
  makeIsOrderedCommRing : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_
  makeIsOrderedCommRing = OCR where
    OCR : IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_
    IsOrderedCommRing.isCommRing OCR = makeIsCommRing
      is-setR +Assoc +IdR +InvR +Comm ·Assoc ·IdR ·DistR+ ·Comm
    IsOrderedCommRing.isPseudolattice OCR = makeIsPseudolattice
      is-setR is-prop-valued≤ is-refl is-trans≤ is-antisym
      is-meet-semipseudolattice is-join-semipseudolattice
    IsOrderedCommRing.isStrictOrder OCR =
      isstrictorder is-setR is-prop-valued is-irrefl is-trans is-asym is-weakly-linear
    IsOrderedCommRing.<-≤-weaken OCR = <-≤-weaken
    IsOrderedCommRing.≤≃¬> OCR = ≤≃¬>
    IsOrderedCommRing.+MonoR≤ OCR = +MonoR≤
    IsOrderedCommRing.+MonoR< OCR = +MonoR<
    IsOrderedCommRing.posSum→pos∨pos OCR = posSum→pos∨pos
    IsOrderedCommRing.<-≤-trans OCR = <-≤-trans
    IsOrderedCommRing.≤-<-trans OCR = ≤-<-trans
    IsOrderedCommRing.·MonoR≤ OCR = ·MonoR≤
    IsOrderedCommRing.·MonoR< OCR = ·MonoR<
    IsOrderedCommRing.·CancelR< OCR = ·CancelR<
    IsOrderedCommRing.0<1 OCR = 0<1

OrderedCommRing→PseudoLattice : OrderedCommRing ℓ ℓ' → Pseudolattice ℓ ℓ'
OrderedCommRing→PseudoLattice R .fst = R .fst
OrderedCommRing→PseudoLattice R .snd = pseudolatticestr _ isPseudolattice where
  open OrderedCommRingStr (str R)

OrderedCommRing→CommRing : OrderedCommRing ℓ ℓ' → CommRing ℓ
OrderedCommRing→CommRing R .fst = R .fst
OrderedCommRing→CommRing R .snd = commringstr _ _ _ _ _ isCommRing where
  open OrderedCommRingStr (str R)

record IsOrderedCommRingHom {ℓ<≤} {ℓ<≤'} {A : Type ℓ} {B : Type ℓ'}
  (R : OrderedCommRingStr ℓ<≤ A)
  (f : A → B)
  (S : OrderedCommRingStr ℓ<≤' B)
  : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ<≤ ℓ<≤'))))
  where
  no-eta-equality
  private
    module R = OrderedCommRingStr R
    module S = OrderedCommRingStr S

  field
    pres0    : f R.0r ≡ S.0r
    pres1    : f R.1r ≡ S.1r
    pres+    : (x y : A) → f (x R.+ y) ≡ f x S.+ f y
    pres·    : (x y : A) → f (x R.· y) ≡ f x S.· f y
    pres-    : (x : A) → f (R.- x) ≡ S.- (f x)
    pres≤    : (x y : A) → x R.≤ y → f x S.≤ f y
    reflect< : (x y : A) → f x S.< f y → x R.< y

unquoteDecl IsOrderedCommRingHomIsoΣ = declareRecordIsoΣ IsOrderedCommRingHomIsoΣ (quote IsOrderedCommRingHom)

OrderedCommRingHom : ∀ {ℓ<≤} {ℓ<≤'}
                     → (R : OrderedCommRing ℓ ℓ<≤)
                     → (S : OrderedCommRing ℓ' ℓ<≤')
                     → Type _
OrderedCommRingHom R S = Σ[ f ∈ (⟨ R ⟩ → ⟨ S ⟩) ] IsOrderedCommRingHom (R .snd) f (S .snd)

IsOrderedCommRingEquiv : ∀ {ℓ<≤} {ℓ<≤'} {A : Type ℓ} {B : Type ℓ'}
                         → (R : OrderedCommRingStr ℓ<≤  A)
                         → (e : A ≃ B)
                         → (S : OrderedCommRingStr ℓ<≤' B)
                         → Type _
IsOrderedCommRingEquiv R e S = IsOrderedCommRingHom R (e .fst) S

OrderedCommRingEquiv : ∀ {ℓ<≤} {ℓ<≤'}
                       → (R : OrderedCommRing ℓ ℓ<≤)
                       → (S : OrderedCommRing ℓ' ℓ<≤')
                       → Type _
OrderedCommRingEquiv R S = Σ[ e ∈ (R .fst ≃ S .fst) ] IsOrderedCommRingEquiv (R .snd) e (S .snd)

OrderedCommRingEquiv→OrderedCommRingHom : ∀ {ℓ<≤} {ℓ<≤'}
                                          → {A : OrderedCommRing ℓ  ℓ<≤}
                                          → {B : OrderedCommRing ℓ' ℓ<≤'}
                                          → OrderedCommRingEquiv A B
                                          → OrderedCommRingHom A B
OrderedCommRingEquiv→OrderedCommRingHom (e , eIsHom) = e .fst , eIsHom

isPropIsOrderedCommRing : {R : Type ℓ}
                          → (0r 1r : R)
                          → (_+_ _·_ : R → R → R) (-_ : R → R)
                          → (_<_ _≤_ : R → R → Type ℓ')
                          → isProp (IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_)
isPropIsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_ = isOfHLevelRetractFromIso 1
  IsOrderedCommRingIsoΣ $
    isPropΣ (isPropIsCommRing _ _ _ _ _) λ isCR →
    isPropΣ (isPropIsPseudolattice _) λ isPL →
    isPropΣ (isPropIsStrictOrder _) λ isSO →
    isProp× (isPropΠ3 λ _ _ _ → isPL .IsPseudolattice.is-prop-valued _ _) $
    isProp× (isPropΠ2 λ x y → isOfHLevel≃ 1
      (IsPoset.is-prop-valued (IsPseudolattice.isPoset isPL) x y)
      (isProp¬ (y < x))) $
    isProp× (isPropΠ4 λ _ _ _ _ → isPL .IsPseudolattice.is-prop-valued _ _) $
    isProp× (isPropΠ4 λ _ _ _ _ → isSO .IsStrictOrder.is-prop-valued _ _) $
    isProp× (isPropΠ3 λ _ _ _ → PT.squash₁) $
    isProp× (isPropΠ5 λ _ _ _ _ _ → isSO .IsStrictOrder.is-prop-valued _ _) $
    isProp× (isPropΠ5 λ _ _ _ _ _ → isSO .IsStrictOrder.is-prop-valued _ _) $
    isProp× (isPropΠ5 λ _ _ _ _ _ → isPL .IsPseudolattice.is-prop-valued _ _) $
    isProp× (isPropΠ5 λ _ _ _ _ _ → isSO .IsStrictOrder.is-prop-valued _ _) $
    isProp× (isPropΠ5 λ _ _ _ _ _ → isSO .IsStrictOrder.is-prop-valued _ _)
            (isSO .IsStrictOrder.is-prop-valued _ _)

isPropIsOrderedCommRingHom : ∀ {ℓ<≤} {ℓ<≤'} {A : Type ℓ} {B : Type ℓ'}
                           → (R : OrderedCommRingStr ℓ<≤ A)
                           → (f : A → B)
                           → (S : OrderedCommRingStr ℓ<≤' B)
                           → isProp (IsOrderedCommRingHom R f S)
isPropIsOrderedCommRingHom R f S = isOfHLevelRetractFromIso 1 IsOrderedCommRingHomIsoΣ $
  isProp× (S.is-set _ _) $
  isProp× (S.is-set _ _) $
  isProp× (isPropΠ2 λ _ _ → S.is-set _ _) $
  isProp× (isPropΠ2 λ _ _ → S.is-set _ _) $
  isProp× (isPropΠ  λ _ → S.is-set _ _) $
  isProp× (isPropΠ3 λ _ _ _ → S.is-prop-valued≤ _ _) $
          (isPropΠ3 λ _ _ _ → R.is-prop-valued< _ _)
  where
    open module R = OrderedCommRingStr R
    open module S = OrderedCommRingStr S

isSetOrderedCommRingHom : (R : OrderedCommRing ℓ ℓ<≤) (S : OrderedCommRing ℓ' ℓ<≤')
                        → isSet (OrderedCommRingHom R S)
isSetOrderedCommRingHom R S = isSetΣSndProp (isSetΠ λ _ → is-set) (λ f →
  isPropIsOrderedCommRingHom (snd R) f (snd S))
    where open OrderedCommRingStr (str S) using (is-set)

isSetOrderedCommRingEquiv : (A : OrderedCommRing ℓ ℓ<≤) (B : OrderedCommRing ℓ' ℓ<≤')
                          → isSet (OrderedCommRingEquiv A B)
isSetOrderedCommRingEquiv A B =
  isSetΣSndProp (isOfHLevel≃ 2 A.is-set B.is-set)
                (λ e → isPropIsOrderedCommRingHom (snd A) (fst e) (snd B))
  where
  module A = OrderedCommRingStr (str A)
  module B = OrderedCommRingStr (str B)

module _
  {R : OrderedCommRing ℓ  ℓ<≤}
  {S : OrderedCommRing ℓ' ℓ<≤'}
  {f : ⟨ R ⟩ → ⟨ S ⟩} where

  private
    module R = OrderedCommRingStr (str R)
    module S = OrderedCommRingStr (str S)
    RCR = OrderedCommRing→CommRing R
    SCR = OrderedCommRing→CommRing S

  module _
    (p1 : f R.1r ≡ S.1r)
    (p+ : (x y : ⟨ R ⟩) → f (x R.+ y) ≡ f x S.+ f y)
    (p· : (x y : ⟨ R ⟩) → f (x R.· y) ≡ f x S.· f y)
    (p≤ : (x y : ⟨ R ⟩) → x R.≤ y → f x S.≤ f y)
    (p<⁻ : (x y : ⟨ R ⟩) → f x S.< f y → x R.< y)
    where

    open IsOrderedCommRingHom

    private
      fpres0 : _
      fpres0 =
        f R.0r ≡⟨ solve! SCR ⟩
        f R.0r S.+ f R.0r S.- f R.0r ≡⟨ sym $ cong (S._- f R.0r) (p+ R.0r R.0r) ⟩
        f (R.0r R.+ R.0r) S.- f R.0r ≡⟨ cong ((S._- f R.0r) ∘ f) (solve! RCR) ⟩
        f R.0r S.- f R.0r            ≡⟨ solve! SCR ⟩
        S.0r                         ∎

    makeIsOrderedCommRingHom : IsOrderedCommRingHom (str R) f (str S)
    makeIsOrderedCommRingHom .pres0    = fpres0
    makeIsOrderedCommRingHom .pres1    = p1
    makeIsOrderedCommRingHom .pres+    = p+
    makeIsOrderedCommRingHom .pres·    = p·
    makeIsOrderedCommRingHom .pres-    = λ x →
      f (R.- x)                 ≡⟨ solve! SCR ⟩
      f (R.- x) S.+ f x S.- f x ≡⟨ sym $ cong (S._- f x) (p+ (R.- x) x) ⟩
      f (R.- x R.+ x) S.- f x   ≡⟨ cong ((S._- f x) ∘ f) (solve! RCR) ⟩
      f R.0r S.- f x            ≡⟨ cong (S._- (f x)) fpres0 ⟩
      S.0r S.- f x              ≡⟨ solve! SCR ⟩
      S.- f x                   ∎
    makeIsOrderedCommRingHom .pres≤    = p≤
    makeIsOrderedCommRingHom .reflect< = p<⁻

_$ocr_ : {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
       → (φ : OrderedCommRingHom R S) → (x : ⟨ R ⟩) → ⟨ S ⟩
φ $ocr x = φ .fst x

opaque
  OrderedCommRingHom≡ : {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
                      → {φ ψ : OrderedCommRingHom R S}
                      → fst φ ≡ fst ψ
                      → φ ≡ ψ
  OrderedCommRingHom≡ = Σ≡Prop λ f → isPropIsOrderedCommRingHom _ f _

  OrderedCommRingHomPathP : (R : OrderedCommRing ℓ ℓ<≤) (S T : OrderedCommRing ℓ' ℓ<≤')
                          → (p : S ≡ T)
                          → (φ : OrderedCommRingHom R S)
                          → (ψ : OrderedCommRingHom R T)
                          → PathP (λ i → R .fst → p i .fst) (φ .fst) (ψ .fst)
                          → PathP (λ i → OrderedCommRingHom R (p i)) φ ψ
  OrderedCommRingHomPathP R S T p φ ψ q = ΣPathP (q , isProp→PathP (λ _ →
    isPropIsOrderedCommRingHom _ _ _) _ _)

record IsOrderedCommRingMono {A : Type ℓ} {B : Type ℓ'}
  (R : OrderedCommRingStr ℓ<≤ A)
  (f : A → B)
  (S : OrderedCommRingStr ℓ<≤' B)
  : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ<≤ ℓ<≤'))))
  where
  no-eta-equality
  private
    module R = OrderedCommRingStr R
    module S = OrderedCommRingStr S

  field
    pres0    : f R.0r ≡ S.0r
    pres1    : f R.1r ≡ S.1r
    pres+    : (x y : A) → f (x R.+ y) ≡ f x S.+ f y
    pres·    : (x y : A) → f (x R.· y) ≡ f x S.· f y
    pres-    : (x : A) → f (R.- x) ≡ S.- (f x)
    pres≤    : (x y : A) → x R.≤ y → f x S.≤ f y
    pres<    : (x y : A) → x R.< y → f x S.< f y
    reflect< : (x y : A) → f x S.< f y → x R.< y

unquoteDecl IsOrderedCommRingMonoIsoΣ = declareRecordIsoΣ IsOrderedCommRingMonoIsoΣ (quote IsOrderedCommRingMono)

OrderedCommRingMono _↣_ : ∀ {ℓ<≤} {ℓ<≤'}
                        → (R : OrderedCommRing ℓ ℓ<≤)
                        → (S : OrderedCommRing ℓ' ℓ<≤')
                        → Type _
OrderedCommRingMono R S = Σ[ f ∈ (⟨ R ⟩ → ⟨ S ⟩) ] IsOrderedCommRingMono (R .snd) f (S .snd)
_↣_ = OrderedCommRingMono

module _
  {R : OrderedCommRing ℓ  ℓ<≤}
  {S : OrderedCommRing ℓ' ℓ<≤'}
  {f : ⟨ R ⟩ → ⟨ S ⟩} where

  private
    module R = OrderedCommRingStr (str R)
    module S = OrderedCommRingStr (str S)

  module _
    (p1 : f R.1r ≡ S.1r)
    (p+ : (x y : ⟨ R ⟩) → f (x R.+ y) ≡ f x S.+ f y)
    (p· : (x y : ⟨ R ⟩) → f (x R.· y) ≡ f x S.· f y)
    (p≤ : (x y : ⟨ R ⟩) → x R.≤ y → f x S.≤ f y)
    (p< : (x y : ⟨ R ⟩) → x R.< y → f x S.< f y)
    (p<⁻ : (x y : ⟨ R ⟩) → f x S.< f y → x R.< y)
    where

    open IsOrderedCommRingMono

    makeIsOrderedCommRingMono : IsOrderedCommRingMono (str R) f (str S)
    makeIsOrderedCommRingMono = isOCRMono
      where
        OCRHom : IsOrderedCommRingHom (str R) f (str S)
        OCRHom = makeIsOrderedCommRingHom p1 p+ p· p≤ p<⁻

        isOCRMono : IsOrderedCommRingMono (str R) f (str S)
        isOCRMono .pres0 = OCRHom .IsOrderedCommRingHom.pres0
        isOCRMono .pres1 = OCRHom .IsOrderedCommRingHom.pres1
        isOCRMono .pres+ = OCRHom .IsOrderedCommRingHom.pres+
        isOCRMono .pres· = OCRHom .IsOrderedCommRingHom.pres·
        isOCRMono .pres- = OCRHom .IsOrderedCommRingHom.pres-
        isOCRMono .pres≤ = OCRHom .IsOrderedCommRingHom.pres≤
        isOCRMono .pres< = p<
        isOCRMono .reflect< = OCRHom .IsOrderedCommRingHom.reflect<

  module _ (isMonof : IsOrderedCommRingMono (str R) f (str S)) where

    isOrderedCommRingMono→reflect≤ : ∀ x y → f x S.≤ f y → x R.≤ y
    isOrderedCommRingMono→reflect≤ x y fx≤fy =
      invEq (R.≤≃¬> x y) $ equivFun (S.≤≃¬> (f x) (f y)) fx≤fy ∘ pres< y x
      where open IsOrderedCommRingMono isMonof

    isOrderedCommRingMono→isOrderedCommRingHom : IsOrderedCommRingHom (str R) f (str S)
    isOrderedCommRingMono→isOrderedCommRingHom = isOCRHom
      where
        open IsOrderedCommRingHom
        isOCRHom : IsOrderedCommRingHom _ _ _
        isOCRHom .pres0    = isMonof .IsOrderedCommRingMono.pres0
        isOCRHom .pres1    = isMonof .IsOrderedCommRingMono.pres1
        isOCRHom .pres+    = isMonof .IsOrderedCommRingMono.pres+
        isOCRHom .pres·    = isMonof .IsOrderedCommRingMono.pres·
        isOCRHom .pres-    = isMonof .IsOrderedCommRingMono.pres-
        isOCRHom .pres≤    = isMonof .IsOrderedCommRingMono.pres≤
        isOCRHom .reflect< = isMonof .IsOrderedCommRingMono.reflect<

isPropIsOrderedCommRingMono : ∀ {ℓ<≤} {ℓ<≤'} {A : Type ℓ} {B : Type ℓ'}
                            → (R : OrderedCommRingStr ℓ<≤ A)
                            → (f : A → B)
                            → (S : OrderedCommRingStr ℓ<≤' B)
                            → isProp (IsOrderedCommRingMono R f S)
isPropIsOrderedCommRingMono R f S = isOfHLevelRetractFromIso 1 IsOrderedCommRingMonoIsoΣ $
  isProp× (S.is-set _ _) $
  isProp× (S.is-set _ _) $
  isProp× (isPropΠ2 λ _ _ → S.is-set _ _) $
  isProp× (isPropΠ2 λ _ _ → S.is-set _ _) $
  isProp× (isPropΠ  λ _ → S.is-set _ _) $
  isProp× (isPropΠ3 λ _ _ _ → S.is-prop-valued≤ _ _) $
  isProp× (isPropΠ3 λ _ _ _ → S.is-prop-valued< _ _)
          (isPropΠ3 λ _ _ _ → R.is-prop-valued< _ _)
  where
    open module R = OrderedCommRingStr R
    open module S = OrderedCommRingStr S

isSetOrderedCommRingMono : (R : OrderedCommRing ℓ ℓ<≤) (S : OrderedCommRing ℓ' ℓ<≤')
                        → isSet (OrderedCommRingMono R S)
isSetOrderedCommRingMono R S = isSetΣSndProp (isSetΠ λ _ → is-set) (λ f →
  isPropIsOrderedCommRingMono (snd R) f (snd S))
    where open OrderedCommRingStr (str S) using (is-set)

opaque
  OrderedCommRingMono≡ : {R : OrderedCommRing ℓ ℓ<≤} {S : OrderedCommRing ℓ' ℓ<≤'}
                       → {φ ψ : OrderedCommRingMono R S}
                       → fst φ ≡ fst ψ
                       → φ ≡ ψ
  OrderedCommRingMono≡ = Σ≡Prop λ f → isPropIsOrderedCommRingMono _ f _

  OrderedCommRingMonoPathP : (R : OrderedCommRing ℓ ℓ<≤) (S T : OrderedCommRing ℓ' ℓ<≤')
                           → (p : S ≡ T)
                           → (φ : OrderedCommRingMono R S)
                           → (ψ : OrderedCommRingMono R T)
                           → PathP (λ i → R .fst → p i .fst) (φ .fst) (ψ .fst)
                           → PathP (λ i → OrderedCommRingMono R (p i)) φ ψ
  OrderedCommRingMonoPathP R S T p φ ψ q = ΣPathP (q , isProp→PathP (λ _ →
    isPropIsOrderedCommRingMono _ _ _) _ _)
