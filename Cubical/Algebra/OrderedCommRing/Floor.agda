module Cubical.Algebra.OrderedCommRing.Floor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Fast.Int renaming
  (ℤOrderedCommRing to ℤOCR)
open import Cubical.Algebra.OrderedCommRing.Morphisms
open import Cubical.Algebra.Ring

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fast.Int as ℤ hiding (_+_ ; _-_ ; -_ ; _·_)
import Cubical.Data.Fast.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' : Level

-- `OrderedCommRingMono ℤOCR R` is contractible, but we keep it as part of the data,
-- as for specific OCR, there are more efficient implementation for this function,
-- rather than iteratively summing the unit of the ring.
-- For instance, with R = ℚ , the underlying function is just λ n → [ n / 1 ]
module FloorCeil
  (R : OrderedCommRing ℓ ℓ')
  ((ι , ιMono) : OrderedCommRingMono ℤOCR R)
  where

  open OrderedCommRingStr (str R) renaming
    (is-prop-valued< to is-prop< ; is-prop-valued≤ to is-prop≤)
  open IsOrderedCommRingMono ιMono
  open OrderedCommRingReasoning R
  open OrderedCommRingTheory R
  open RingTheory (OrderedCommRing→Ring R)

  record Floor (r : ⟨ R ⟩) : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    field
      ⌊_⌋    : ℤ
      ⌊⌋≤    : ι ⌊_⌋ ≤ r
      <suc⌊⌋ : r < ι (sucℤ ⌊_⌋)

  unquoteDecl FloorIsoΣ = declareRecordIsoΣ FloorIsoΣ (quote Floor)

  record Ceil (r : ⟨ R ⟩) : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    field
      ⌈_⌉     : ℤ
      ≤⌈⌉     : r ≤ ι ⌈_⌉
      pred⌈⌉< : ι (predℤ ⌈_⌉) < r

  unquoteDecl CeilIsoΣ = declareRecordIsoΣ CeilIsoΣ (quote Ceil)

  private
    lemmaFloorProp : ∀ r k h → r < ι (sucℤ k) → ι h ≤ r → ¬ (k ℤ.< h)
    lemmaFloorProp r k h r<ι1+k ιh≤r k<h = is-irrefl r $ begin<
      r          <⟨ r<ι1+k ⟩
      ι (sucℤ k) ≤⟨ pres≤ _ _ (ℤ.<→suc≤ k<h) ⟩
      ι h        ≤⟨ ιh≤r ⟩
      r          ◾

    lemmaCeilProp : ∀ r k h → r ≤ ι k → ι (predℤ h) < r → ¬ (k ℤ.< h)
    lemmaCeilProp r k h r≤ιk ιh-1<r k<h = is-irrefl r $ begin<
      r           ≤⟨ r≤ιk ⟩
      ι k         ≤⟨ pres≤ _ _ (ℤ.<→≤pred k<h) ⟩
      ι (predℤ h) <⟨ ιh-1<r ⟩
      r           ◾

  isPropFloor : ∀ r → isProp (Floor r)
  isPropFloor r = isOfHLevelRetractFromIso 1 FloorIsoΣ proof where
    proof : isProp (Σ[ k ∈ ℤ ] (ι k ≤ r) × (r < ι (sucℤ k)))
    proof (k , ιk≤r , r<ι1+k) (h , ιh≤r , r<ι1+h) with k ℤ.≟ h
    ... | ℤ.lt k<h = ⊥.rec (lemmaFloorProp r k h r<ι1+k ιh≤r k<h)
    ... | ℤ.eq k≡h = Σ≡Prop (λ _ → isProp× (is-prop≤ _ _) (is-prop< _ _)) k≡h
    ... | ℤ.gt k>h = ⊥.rec (lemmaFloorProp r h k r<ι1+h ιk≤r k>h)

  isPropCeil : ∀ r → isProp (Ceil r)
  isPropCeil r = isOfHLevelRetractFromIso 1 CeilIsoΣ proof where
    proof : isProp (Σ[ k ∈ ℤ ] (r ≤ ι k) × (ι (predℤ k) < r))
    proof (k , ιk-1<r , r≤ιk) (h , ιh-1<r , r≤ιh) with k ℤ.≟ h
    ... | ℤ.lt k<h = ⊥.rec (lemmaCeilProp r k h ιk-1<r r≤ιh k<h)
    ... | ℤ.eq k≡h = Σ≡Prop (λ _ → isProp× (is-prop≤ _ _) (is-prop< _ _)) k≡h
    ... | ℤ.gt k>h = ⊥.rec (lemmaCeilProp r h k ιh-1<r r≤ιk k>h)

  Floor→Ceil- : ∀ r → Floor r → Ceil (- r)
  Floor→Ceil- r x .Ceil.⌈_⌉     = ℤ.- Floor.⌊ x ⌋
  Floor→Ceil- r x .Ceil.≤⌈⌉     = subst (_ ≤_) (sym (pres- _)) (-Flip≤ _ r (Floor.⌊⌋≤ x))
  Floor→Ceil- r x .Ceil.pred⌈⌉< = subst (_< _) (sym (pres- _) ∙ cong ι (-sucℤ _))
    (-Flip< r _ (Floor.<suc⌊⌋ x))

  -Floor→Ceil : ∀ r → Floor (- r) → Ceil r
  -Floor→Ceil r x .Ceil.⌈_⌉     = ℤ.- Floor.⌊ x ⌋
  -Floor→Ceil r x .Ceil.≤⌈⌉     = subst2 _≤_ (-Idempotent r) (sym (pres- _))
    (-Flip≤ _ _ (Floor.⌊⌋≤ x))
  -Floor→Ceil r x .Ceil.pred⌈⌉< = subst2 _<_
    (sym (pres- _) ∙ cong ι (-sucℤ _)) (-Idempotent r) (-Flip< _ _ (Floor.<suc⌊⌋ x))

  module FloorProperties (floor : ∀ r → Floor r) where

    ⌊_⌋ : ⟨ R ⟩ → ℤ
    ⌊_⌋ = Floor.⌊_⌋ ∘ floor

    private
      floorℤ : ∀ k → Floor (ι k)
      floorℤ k .Floor.⌊_⌋    = k
      floorℤ k .Floor.⌊⌋≤    = is-refl (ι k)
      floorℤ k .Floor.<suc⌊⌋ = pres< k (sucℤ k) ℤ.<-sucℤ

    isContrFloor : ∀ r → isContr (Floor r)
    isContrFloor r .fst = floor r
    isContrFloor r .snd = isPropFloor r (floor r)

    isUniqueFloor : ∀ {r} → (x : Floor r) → ⌊ r ⌋ ≡ Floor.⌊ x ⌋
    isUniqueFloor = cong Floor.⌊_⌋ ∘ snd (isContrFloor _)

    ⌊⌋∘ι≡id : ∀ k → ⌊ ι k ⌋ ≡ k
    ⌊⌋∘ι≡id = isUniqueFloor ∘ floorℤ

    ⌊0⌋≡0 : ⌊ 0r ⌋ ≡ 0
    ⌊0⌋≡0 = sym (cong ⌊_⌋ pres0) ∙ ⌊⌋∘ι≡id 0

    ⌊1⌋≡1 : ⌊ 1r ⌋ ≡ 1
    ⌊1⌋≡1 = sym (cong ⌊_⌋ pres1) ∙ ⌊⌋∘ι≡id 1

    ⌊⌋Mono≤ : ∀ x y → x ≤ y → ⌊ x ⌋ ℤ.≤ ⌊ y ⌋
    ⌊⌋Mono≤ x y x≤y = ℤ.<suc→≤ $ reflect< ⌊ x ⌋ (sucℤ ⌊ y ⌋) $ begin<
      ι ⌊ x ⌋         ≤⟨ floor x .Floor.⌊⌋≤ ⟩
      x              ≤⟨ x≤y ⟩
      y              <⟨ floor y .Floor.<suc⌊⌋ ⟩
      ι (sucℤ ⌊ y ⌋) ◾

    0≤→0≤⌊⌋ : ∀ r → 0r ≤ r → 0 ℤ.≤ ⌊ r ⌋
    0≤→0≤⌊⌋ r = ℤ.recompute≤ ∘ subst (ℤ._≤ ⌊ r ⌋) ⌊0⌋≡0 ∘ ⌊⌋Mono≤ 0r r

  module CeilProperties (ceil : ∀ r → Ceil r) where

    ⌈_⌉ : ⟨ R ⟩ → ℤ
    ⌈_⌉ = Ceil.⌈_⌉ ∘ ceil

    private
      ceilℤ : ∀ k → Ceil (ι k)
      ceilℤ k .Ceil.⌈_⌉     = k
      ceilℤ k .Ceil.≤⌈⌉     = is-refl (ι k)
      ceilℤ k .Ceil.pred⌈⌉< = pres< (predℤ k) k (ℤ.≤→pred< ℤ.isRefl≤)

    isContrCeil : ∀ r → isContr (Ceil r)
    isContrCeil r .fst = ceil r
    isContrCeil r .snd = isPropCeil r (ceil r)

    isUniqueCeil : ∀ {r} → (x : Ceil r) → ⌈ r ⌉ ≡ Ceil.⌈ x ⌉
    isUniqueCeil = cong Ceil.⌈_⌉ ∘ snd (isContrCeil _)

    ⌈⌉∘ι≡id : ∀ k → ⌈ ι k ⌉ ≡ k
    ⌈⌉∘ι≡id = isUniqueCeil ∘ ceilℤ

    ⌈0⌉≡0 : ⌈ 0r ⌉ ≡ 0
    ⌈0⌉≡0 = sym (cong ⌈_⌉ pres0) ∙ ⌈⌉∘ι≡id 0

    ⌈1⌉≡1 : ⌈ 1r ⌉ ≡ 1
    ⌈1⌉≡1 = sym (cong ⌈_⌉ pres1) ∙ ⌈⌉∘ι≡id 1

    ⌈⌉Mono≤ : ∀ x y → x ≤ y → ⌈ x ⌉ ℤ.≤ ⌈ y ⌉
    ⌈⌉Mono≤ x y x≤y = ℤ.pred<→≤ $ reflect< (predℤ ⌈ x ⌉) ⌈ y ⌉ $ begin<
      ι (predℤ ⌈ x ⌉) <⟨ ceil x .Ceil.pred⌈⌉< ⟩
      x              ≤⟨ x≤y ⟩
      y              ≤⟨ ceil y .Ceil.≤⌈⌉ ⟩
      ι ⌈ y ⌉ ◾

    0<→0<⌈⌉ : ∀ r → 0r < r → 0 ℤ.< ⌈ r ⌉
    0<→0<⌈⌉ r 0<r = reflect< 0 ⌈ r ⌉ $ begin<
      ι 0 ≡→≤⟨ pres0 ⟩ 0r <⟨ 0<r ⟩ r ≤⟨ ceil r .Ceil.≤⌈⌉ ⟩ ι ⌈ r ⌉ ◾
