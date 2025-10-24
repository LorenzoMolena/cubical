module Cubical.Relation.Binary.Order.Pseudolattice.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset renaming (
  isPseudolattice to pseudolattice ;
  isPropIsPseudolattice to is-prop-is-pseudolattice)

open BinaryRelation

private
  variable
    ℓ ℓ' : Level

record IsPseudolattice {L : Type ℓ} (_≤_ : L → L → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor ispseudolattice

  field
    isPoset : IsPoset _≤_
    isPseudolattice : pseudolattice (poset L _≤_ isPoset)

  open IsPoset isPoset public

  _∧l_ : L → L → L
  a ∧l b = (isPseudolattice .fst a b) .fst

  _∨l_ : L → L → L
  a ∨l b = (isPseudolattice .snd a b) .fst

  infixl 7 _∧l_
  infixl 6 _∨l_


unquoteDecl IsPseudolatticeIsoΣ = declareRecordIsoΣ IsPseudolatticeIsoΣ (quote IsPseudolattice)

record PseudolatticeStr (ℓ' : Level) (L : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor pseudolatticestr

  field
    _≤_ : L → L → Type ℓ'
    is-pseudolattice : IsPseudolattice _≤_

  open IsPseudolattice is-pseudolattice public


unquoteDecl PseudolatticeStrIsoΣ = declareRecordIsoΣ PseudolatticeStrIsoΣ (quote PseudolatticeStr)

Pseudolattice : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
Pseudolattice ℓ ℓ' = TypeWithStr ℓ (PseudolatticeStr ℓ')

module _
  {L : Type ℓ} {_≤_ : L → L → Type ℓ'}
  (is-setL : isSet L)
  (is-prop-valued : isPropValued _≤_)
  (is-refl : isRefl _≤_)
  (is-trans : isTrans _≤_)
  (is-antisym : isAntisym _≤_)
  (is-meet-semipseudolattice : isMeetSemipseudolattice (poset L _≤_
    (isposet is-setL is-prop-valued is-refl is-trans is-antisym)))
  (is-join-semipseudolattice : isJoinSemipseudolattice (poset L _≤_
    (isposet is-setL is-prop-valued is-refl is-trans is-antisym))) where

  makeIsPseudolattice : IsPseudolattice _≤_
  makeIsPseudolattice = PS where
    PS : IsPseudolattice _≤_
    PS .IsPseudolattice.isPoset = isposet is-setL is-prop-valued is-refl is-trans is-antisym
    PS .IsPseudolattice.isPseudolattice .fst = is-meet-semipseudolattice
    PS .IsPseudolattice.isPseudolattice .snd = is-join-semipseudolattice

module _
  (P : Poset ℓ ℓ') (_∧_ _∨_ : ⟨ P ⟩ → ⟨ P ⟩ → ⟨ P ⟩) where
  open PosetStr (str P) renaming (_≤_ to infix 8 _≤_)
  module _
    (π₁ : ∀ {a b x} → x ≤ a ∧ b → x ≤ a)
    (π₂ : ∀ {a b x} → x ≤ a ∧ b → x ≤ b)
    (ϕ  : ∀ {a b x} → x ≤ a → x ≤ b → x ≤ a ∧ b)
    (ι₁ : ∀ {a b x} → a ∨ b ≤ x → a ≤ x)
    (ι₂ : ∀ {a b x} → a ∨ b ≤ x → b ≤ x)
    (ψ  : ∀ {a b x} → a ≤ x → b ≤ x → a ∨ b ≤ x) where

    makePseudolatticeFromPoset : Pseudolattice ℓ ℓ'
    makePseudolatticeFromPoset .fst = ⟨ P ⟩
    makePseudolatticeFromPoset .snd .PseudolatticeStr._≤_ = (str P) .PosetStr._≤_
    makePseudolatticeFromPoset .snd .PseudolatticeStr.is-pseudolattice = isPL where
      isPL : IsPseudolattice _≤_
      isPL .IsPseudolattice.isPoset = isPoset
      isPL .IsPseudolattice.isPseudolattice .fst a b .fst = a ∧ b
      isPL .IsPseudolattice.isPseudolattice .fst a b .snd x = propBiimpl→Equiv
        (is-prop-valued _ _)
        (isProp× (is-prop-valued _ _) (is-prop-valued _ _))
        (λ x≤a∧b → π₁ x≤a∧b , π₂ x≤a∧b)
        (uncurry ϕ)
      isPL .IsPseudolattice.isPseudolattice .snd a b .fst = a ∨ b
      isPL .IsPseudolattice.isPseudolattice .snd a b .snd x = propBiimpl→Equiv
        (is-prop-valued _ _)
        (isProp× (is-prop-valued _ _) (is-prop-valued _ _))
        (λ a∨b≤x → ι₁ a∨b≤x , ι₂ a∨b≤x)
        (uncurry ψ)

isPropIsPseudolattice : {L : Type ℓ} (_≤_ : L → L → Type ℓ') → isProp (IsPseudolattice _≤_)
isPropIsPseudolattice {L = L} _≤_ = isOfHLevelRetractFromIso 1
  IsPseudolatticeIsoΣ $ isPropΣ
  (isPropIsPoset _≤_) λ isPoset →
  is-prop-is-pseudolattice (poset L _≤_ isPoset)

isPseudolattice→isProp≤≡≤' : {L : Type ℓ} → {_≤_ : L → L → Type ℓ'}
                           → IsPseudolattice _≤_
                           → {_≤'_ : L → L → Type ℓ'}
                           → isProp (_≤_ ≡ _≤'_)
isPseudolattice→isProp≤≡≤' isPL≤ p q i j x y =
  isOfHLevel⁺≡ₗ 0 (is-prop-valued x y) (λ i → p i x y) (λ i → q i x y) i j
  where open IsPseudolattice isPL≤

isSetPseudolatticeStr : {L : Type ℓ} → isSet (PseudolatticeStr ℓ' L)
isSetPseudolatticeStr {L = L} = isOfHLevelRetractFromIso 2
  PseudolatticeStrIsoΣ λ (_ , isPL≤) _ p q →
  ΣSquareSet
    (isProp→isSet ∘ isPropIsPseudolattice)
    (isPseudolattice→isProp≤≡≤' isPL≤ (cong fst p) (cong fst q))
