module Cubical.Data.Rationals.Fast.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Logic using (_⊔′_)

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Int.Fast.Base as ℤ using (ℤ)
open import Cubical.Data.Int.Fast.Properties as ℤ using ()
open import Cubical.Data.Int.Fast.Order as ℤ using ()
open import Cubical.Data.Rationals.Fast.Base as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚ
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr; isProp⊎)

open import Cubical.HITs.PropositionalTruncation as ∥₁ using (isPropPropTrunc; ∣_∣₁)
open import Cubical.HITs.SetQuotients renaming (_/_ to _//_)

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

infix 4 _≤_ _<_ _≥_ _>_

private
  ·CommR : (a b c : ℤ) → a ℤ.· b ℤ.· c ≡ a ℤ.· c ℤ.· b
  ·CommR a b c = sym (ℤ.·Assoc a b c) ∙ cong (a ℤ.·_) (ℤ.·Comm b c) ∙ ℤ.·Assoc a c b

  _≤'_ : ℚ → ℚ → hProp ℓ-zero
  _≤'_ = fun
    where
        lemma≤ : ((a , b) (c , d) (e , f) : (ℤ × ℕ₊₁))
                → (c ℤ.· ℕ₊₁→ℤ f ) ≡ (e ℤ.· ℕ₊₁→ℤ d)
                → ((a ℤ.· ℕ₊₁→ℤ d) ℤ.≤ (c ℤ.· ℕ₊₁→ℤ b))
                ≡ ((a ℤ.· ℕ₊₁→ℤ f) ℤ.≤ (e ℤ.· ℕ₊₁→ℤ b))
        lemma≤ (a , b) (c , d) (e , f) cf≡ed = (ua (propBiimpl→Equiv ℤ.isProp≤ ℤ.isProp≤
                (ℤ.≤-·o-cancel ∘
                  subst2 ℤ._≤_ (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                               (·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) ∙
                                cong (ℤ._· ℕ₊₁→ℤ b) cf≡ed ∙
                                ·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
                 ℤ.≤-·o)
                (ℤ.≤-·o-cancel ∘
                  subst2 ℤ._≤_ (·CommR a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d))
                                (·CommR e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) ∙
                                 cong (ℤ._· ℕ₊₁→ℤ b) (sym cf≡ed) ∙
                                 ·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∘
                 ℤ.≤-·o)))

        fun₀ : ℤ × ℕ₊₁ → ℚ → hProp ℓ-zero
        fst (fun₀ (a , b) [ c , d ]) = a ℤ.· ℕ₊₁→ℤ d ℤ.≤ c ℤ.· ℕ₊₁→ℤ b
        snd (fun₀ _ [ _ ]) = ℤ.isProp≤
        fun₀ a/b (eq/ c/d e/f cf≡ed i) = record
          { fst = lemma≤ a/b c/d e/f cf≡ed i
          ; snd = isProp→PathP (λ i → isPropIsProp {A = lemma≤ a/b c/d e/f cf≡ed i}) ℤ.isProp≤ ℤ.isProp≤ i
          }
        fun₀ a/b (squash/ x y p q i j) = isSet→SquareP (λ _ _ → isSetHProp)
          (λ _ → fun₀ a/b x)
          (λ _ → fun₀ a/b y)
          (λ i → fun₀ a/b (p i))
          (λ i → fun₀ a/b (q i)) j i

        toPath : ∀ a/b c/d (x : a/b ∼ c/d) (y : ℚ) → fun₀ a/b y ≡ fun₀ c/d y
        toPath (a , b) (c , d) ad≡cb = elimProp (λ _ → isSetHProp _ _) λ (e , f) →
          Σ≡Prop (λ _ → isPropIsProp) (ua (propBiimpl→Equiv ℤ.isProp≤ ℤ.isProp≤
                (ℤ.≤-·o-cancel ∘
                  subst2 ℤ._≤_ (·CommR a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d) ∙
                                 cong (ℤ._· ℕ₊₁→ℤ f) ad≡cb ∙
                                 ·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                               (·CommR e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∘
                 ℤ.≤-·o)
                (ℤ.≤-·o-cancel ∘
                  subst2 ℤ._≤_ (·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b) ∙
                                 cong (ℤ._· ℕ₊₁→ℤ f) (sym ad≡cb) ∙
                                 ·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                               (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
                 ℤ.≤-·o)))

        fun : ℚ → ℚ → hProp ℓ-zero
        fun [ a/b ] y = fun₀ a/b y
        fun (eq/ a/b c/d ad≡cb i) y = toPath a/b c/d ad≡cb y i
        fun (squash/ x y p q i j) z = isSet→SquareP (λ _ _ → isSetHProp)
          (λ _ → fun x z) (λ _ → fun y z) (λ i → fun (p i) z) (λ i → fun (q i) z) j i

  _<'_ : ℚ → ℚ → hProp ℓ-zero
  _<'_ = fun
    where
        lemma< : ((a , b) (c , d) (e , f) : (ℤ × ℕ₊₁))
                → (c ℤ.· ℕ₊₁→ℤ f ) ≡ (e ℤ.· ℕ₊₁→ℤ d)
                → ((a ℤ.· ℕ₊₁→ℤ d) ℤ.< (c ℤ.· ℕ₊₁→ℤ b))
                ≡ ((a ℤ.· ℕ₊₁→ℤ f) ℤ.< (e ℤ.· ℕ₊₁→ℤ b))
        lemma< (a , b) (c , d) (e , f) cf≡ed = (ua (propBiimpl→Equiv ℤ.isProp< ℤ.isProp<
                (ℤ.<-·o-cancel ∘
                  subst2 ℤ._<_ (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                               (·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) ∙
                                cong (ℤ._· ℕ₊₁→ℤ b) cf≡ed ∙
                                ·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
                 ℤ.<-·o)
                (ℤ.<-·o-cancel ∘
                  subst2 ℤ._<_ (·CommR a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d))
                               (·CommR e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) ∙
                                cong (ℤ._· ℕ₊₁→ℤ b) (sym cf≡ed) ∙
                                ·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b)) ∘
                 ℤ.<-·o)))

        fun₀ : ℤ × ℕ₊₁ → ℚ → hProp ℓ-zero
        fst (fun₀ (a , b) [ c , d ]) = a ℤ.· ℕ₊₁→ℤ d ℤ.< c ℤ.· ℕ₊₁→ℤ b
        snd (fun₀ _ [ _ ]) = ℤ.isProp<
        fun₀ a/b (eq/ c/d e/f cf≡ed i) = record
          { fst = lemma< a/b c/d e/f cf≡ed i
          ; snd = isProp→PathP (λ i → isPropIsProp {A = lemma< a/b c/d e/f cf≡ed i}) ℤ.isProp< ℤ.isProp< i
          }
        fun₀ a/b (squash/ x y p q i j) = isSet→SquareP (λ _ _ → isSetHProp)
          (λ _ → fun₀ a/b x)
          (λ _ → fun₀ a/b y)
          (λ i → fun₀ a/b (p i))
          (λ i → fun₀ a/b (q i)) j i

        toPath : ∀ a/b c/d (x : a/b ∼ c/d) (y : ℚ) → fun₀ a/b y ≡ fun₀ c/d y
        toPath (a , b) (c , d) ad≡cb = elimProp (λ _ → isSetHProp _ _) λ (e , f) →
          Σ≡Prop (λ _ → isPropIsProp) (ua (propBiimpl→Equiv ℤ.isProp< ℤ.isProp<
                (ℤ.<-·o-cancel ∘
                  subst2 ℤ._<_ (·CommR a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d) ∙
                                cong (ℤ._· ℕ₊₁→ℤ f) ad≡cb ∙
                                ·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                               (·CommR e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∘
                 ℤ.<-·o)
                (ℤ.<-·o-cancel ∘
                  subst2 ℤ._<_ (·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b) ∙
                                cong (ℤ._· ℕ₊₁→ℤ f) (sym ad≡cb) ∙
                                ·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                               (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∘
                 ℤ.<-·o)))

        fun : ℚ → ℚ → hProp ℓ-zero
        fun [ a/b ] y = fun₀ a/b y
        fun (eq/ a/b c/d ad≡cb i) y = toPath a/b c/d ad≡cb y i
        fun (squash/ x y p q i j) z = isSet→SquareP (λ _ _ → isSetHProp)
          (λ _ → fun x z) (λ _ → fun y z) (λ i → fun (p i) z) (λ i → fun (q i) z) j i

record _≤_ (m n : ℚ ) : Type₀ where
  constructor inj
  field
    prf : fst (m ≤' n)

record _<_ (m n : ℚ ) : Type₀ where
  constructor inj
  field
    prf : fst (m <' n)

pattern pos≤pos p       = inj (ℤ.pos≤pos p)
pattern negsuc≤pos      = inj ℤ.negsuc≤pos
pattern negsuc≤negsuc p = inj (ℤ.negsuc≤negsuc p)

pattern pos<pos p       = inj (ℤ.pos<pos p)
pattern negsuc<pos      = inj ℤ.negsuc<pos
pattern negsuc<negsuc p = inj (ℤ.negsuc<negsuc p)

_≥_ : ℚ → ℚ → Type₀
m ≥ n = n ≤ m

_>_ : ℚ → ℚ → Type₀
m > n = n < m

_#_ : ℚ → ℚ → Type₀
m # n = (m < n) ⊎ (n < m)

data Trichotomy (m n : ℚ) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : m > n → Trichotomy m n

module _ where
  open BinaryRelation

  isProp≤ : isPropValued _≤_
  isProp≤ m n (inj p) (inj q) = cong inj (snd (m ≤' n) p q)

  isProp< : isPropValued _<_
  isProp< m n (inj p) (inj q) = cong inj (snd (m <' n) p q)

  recompute≤ : ∀ {a b} → a ≤ b → a ≤ b
  recompute≤ = elimProp2 {P = λ a b → a ≤ b → a ≤ b}
                         (λ _ _ → isProp→ (isProp≤ _ _))
                         (λ _ _ → inj ∘ ℤ.recompute≤ ∘ _≤_.prf) _ _

  recompute< : ∀ {a b} → a < b → a < b
  recompute< = elimProp2 {P = λ a b → a < b → a < b}
                         (λ _ _ → isProp→ (isProp< _ _))
                         (λ _ _ → inj ∘ ℤ.recompute< ∘ _<_.prf) _ _

  recompute¬≤ : ∀ {a b} → ¬ (a ≤ b) → ¬ (a ≤ b)
  recompute¬≤ = elimProp2 {P = λ a b → ¬ (a ≤ b) → ¬ (a ≤ b)}
                          (λ _ _ → isProp→ (isProp¬ _))
                          (λ _ _ ¬a≤b → ℤ.recompute¬≤ (¬a≤b ∘ inj) ∘ _≤_.prf) _ _

  recompute¬< : ∀ {a b} → ¬ (a < b) → ¬ (a < b)
  recompute¬< = elimProp2 {P = λ a b → ¬ (a < b) → ¬ (a < b)}
                          (λ _ _ → isProp→ (isProp¬ _))
                          (λ _ _ ¬a<b → ℤ.recompute¬< (¬a<b ∘ inj) ∘ _<_.prf) _ _

  recompute# : ∀ {a b} → a # b → a # b
  recompute# = ⊎.map recompute< recompute<

  recompute¬# : ∀ {a b} → ¬ (a # b) → ¬ (a # b)
  recompute¬# r = ⊎.rec (recompute¬< (r ∘ inl)) (recompute¬< (r ∘ inr))

  isRefl≤ : isRefl _≤_
  isRefl≤ = elimProp {P = λ x → x ≤ x} (λ x → isProp≤ x x) λ _ → inj ℤ.isRefl≤

  isIrrefl< : isIrrefl _<_
  isIrrefl< = elimProp {P = λ x → ¬ x < x} (λ _ → isProp¬ _) λ _ → ℤ.isIrrefl< ∘ _<_.prf

  isAntisym≤ : isAntisym _≤_
  isAntisym≤ =
    elimProp2 {P = λ a b → a ≤ b → b ≤ a → a ≡ b}
              (λ x y → isPropΠ2 λ _ _ → isSetℚ x y)
              λ a b (inj a≤b) (inj b≤a) → eq/ a b (ℤ.isAntisym≤ a≤b b≤a)

  isTrans≤ : isTrans _≤_
  isTrans≤ =
    elimProp3 {P = λ a b c → a ≤ b → b ≤ c → a ≤ c}
              (λ x _ z → isPropΠ2 λ _ _ → isProp≤ x z)
              λ { (a , b) (c , d) (e , f) (inj ad≤cb) (inj cf≤ed) →
                inj (ℤ.≤-·o-cancel
                  (subst (ℤ._≤ e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d)
                    (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                  (ℤ.isTrans≤ (ℤ.≤-·o ad≤cb)
                    (subst2 ℤ._≤_
                      (·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                      (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                      (ℤ.≤-·o cf≤ed))))) }

  isTrans< : isTrans _<_
  isTrans< =
    elimProp3 {P = λ a b c → a < b → b < c → a < c}
              (λ x _ z → isPropΠ2 λ _ _ → isProp< x z)
              λ { (a , b) (c , d) (e , f) (inj ad<cb) (inj cf<ed) →
                inj (ℤ.<-·o-cancel
                  (subst (ℤ._< e ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ d)
                    (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                  (ℤ.isTrans< (ℤ.<-·o ad<cb)
                    (subst2 ℤ._<_
                      (·CommR c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                      (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                      (ℤ.<-·o cf<ed))))) }

  isAsym< : isAsym _<_
  isAsym< = ((recompute¬< ∘_) ∘_) ∘ isIrrefl×isTrans→isAsym _<_ (isIrrefl< , isTrans<)

  isTotal≤ : isTotal _≤_
  isTotal≤ =
    elimProp2 {P = λ a b → (a ≤ b) ⊔′ (b ≤ a)}
              (λ _ _ → isPropPropTrunc)
               λ a b → ∣ lem a b ∣₁
    where
      lem : (a b : ℤ.ℤ × ℕ₊₁) → ([ a ] ≤ [ b ]) ⊎ ([ b ] ≤ [ a ])
      lem (a , b) (c , d) with (a ℤ.· ℕ₊₁→ℤ d) ℤ.≟ (c ℤ.· ℕ₊₁→ℤ b)
      ... | ℤ.lt ad<cb = inl (inj (ℤ.<-weaken ad<cb))
      ... | ℤ.eq ad≡cb = inl (inj (ℤ.recompute≤ $ subst (_ ℤ.≤_) ad≡cb ℤ.isRefl≤))
      ... | ℤ.gt cb<ad = inr (inj (ℤ.<-weaken cb<ad))

  isConnected< : isConnected _<_
  isConnected< =
    elimProp2 {P = λ a b → (¬ a < b) × (¬ b < a) → a ≡ b}
              (λ a b → isProp→ (isSetℚ a b))
               lem
    where
      lem : (a b : ℤ.ℤ × ℕ₊₁) → (¬ [ a ] < [ b ]) × (¬ [ b ] < [ a ]) → [ a ] ≡ [ b ]
      lem (a , b) (c , d) (¬ad<cb , ¬cb<ad) with (a ℤ.· ℕ₊₁→ℤ d) ℤ.≟ (c ℤ.· ℕ₊₁→ℤ b)
      ... | ℤ.lt ad<cb = ⊥.rec (¬ad<cb (inj ad<cb))
      ... | ℤ.eq ad≡cb = eq/ (a , b) (c , d) ad≡cb
      ... | ℤ.gt cb<ad = ⊥.rec (¬cb<ad (inj cb<ad))

  isProp# : isPropValued _#_
  isProp# x y = isProp⊎ (isProp< x y) (isProp< y x) (isAsym< x y)

  isIrrefl# : isIrrefl _#_
  isIrrefl# x (inl x<x) = isIrrefl< x x<x
  isIrrefl# x (inr x<x) = isIrrefl< x x<x

  isSym# : isSym _#_
  isSym# _ _ (inl x<y) = inr x<y
  isSym# _ _ (inr y<x) = inl y<x

  inequalityImplies# : inequalityImplies _#_
  inequalityImplies#
    = elimProp2 {P = λ a b → ¬ a ≡ b → a # b}
                (λ a b → isProp→ (isProp# a b))
                 lem
    where
      lem : (a b : ℤ.ℤ × ℕ₊₁) → ¬ [_] {R = _∼_} a ≡ [ b ] → [ a ] # [ b ]
      lem (a , b) (c , d) ¬a≡b with (a ℤ.· ℕ₊₁→ℤ d) ℤ.≟ (c ℤ.· ℕ₊₁→ℤ b)
      ... | ℤ.lt ad<cb = inl (inj ad<cb)
      ... | ℤ.eq ad≡cb = ⊥.rec (¬a≡b (eq/ (a , b) (c , d) ad≡cb))
      ... | ℤ.gt cb<ad = inr (inj cb<ad)

  isWeaklyLinear< : isWeaklyLinear _<_
  isWeaklyLinear< =
    elimProp3 {P = λ a b c → a < b → (a < c) ⊔′ (c < b)}
              (λ _ _ _ → isProp→ isPropPropTrunc)
               lem
    where
      lem : (a b c : ℤ.ℤ × ℕ₊₁) → [ a ] < [ b ] → ([ a ] < [ c ]) ⊔′ ([ c ] < [ b ])
      lem a b c a<b with discreteℚ [ a ] [ c ]
      ... | yes a≡c = ∣ inr (recompute< (subst (_< [ b ]) a≡c a<b)) ∣₁
      ... | no a≢c = ∣ ⊎.map (λ a<c → a<c)
                             (λ c<a → isTrans< [ c ] [ a ] [ b ] c<a a<b)
                             (inequalityImplies# [ a ] [ c ] a≢c) ∣₁

  isCotrans# : isCotrans _#_
  isCotrans#
    = elimProp3 {P = λ a b c → a # b → (a # c) ⊔′ (b # c)}
                (λ _ _ _ → isProp→ isPropPropTrunc)
                 lem
      where
        lem : (a b c : ℤ.ℤ × ℕ₊₁) → [ a ] # [ b ] → ([ a ] # [ c ]) ⊔′ ([ b ] # [ c ])
        lem a b c a#b with discreteℚ [ b ] [ c ]
        ... | yes b≡c = ∣ inl (recompute# (subst ([ a ] #_) b≡c a#b)) ∣₁
        ... | no  b≢c = ∣ inr (inequalityImplies# [ b ] [ c ] b≢c) ∣₁

≤-+o : ∀ m n o → m ≤ n → m ℚ.+ o ≤ n ℚ.+ o
≤-+o =
  elimProp3 {P = λ a b c → a ≤ b → a ℚ.+ c ≤ b ℚ.+ c}
            (λ x y z → isProp→ (isProp≤ (x ℚ.+ z) (y ℚ.+ z)))
             λ { (a , b) (c , d) (e , f) (inj ad≤cb) →
                inj $ ℤ.recompute≤ $ subst2 ℤ._≤_
                       (cong₂ ℤ._+_
                              (cong (λ x → a ℤ.· ℕ₊₁→ℤ d ℤ.· x)
                                    (ℤ.pos·pos (ℕ₊₁→ℕ f) (ℕ₊₁→ℕ f)) ∙
                                    sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ f)) ∙
                                    cong (a ℤ.·_) (ℤ.·Assoc (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ f) ∙
                                    cong (ℤ._· ℕ₊₁→ℤ f) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                                    sym (ℤ.·Assoc (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))) ∙
                                    ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f) ∙
                                    cong (λ x → a ℤ.· ℕ₊₁→ℤ f ℤ.· x)
                                         (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))))
                              (sym (ℤ.·Assoc (e ℤ.· ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                                   cong (λ x → e ℤ.· ℕ₊₁→ℤ b ℤ.· x)
                                        (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f)))) ∙
                              sym (ℤ.·DistL+ (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b) (ℕ₊₁→ℤ (d ·₊₁ f))))
                       (cong₂ ℤ._+_
                              (cong (λ x → c ℤ.· ℕ₊₁→ℤ b ℤ.· x)
                                    (ℤ.pos·pos (ℕ₊₁→ℕ f) (ℕ₊₁→ℕ f)) ∙
                                    sym (ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ f)) ∙
                                    cong (c ℤ.·_) (ℤ.·Assoc (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ f) ∙
                                    cong (ℤ._· ℕ₊₁→ℤ f) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                                    sym (ℤ.·Assoc (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))) ∙
                                    ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ f) ∙
                                    cong (λ x → c ℤ.· ℕ₊₁→ℤ f ℤ.· x)
                                         (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f))))
                              (cong (ℤ._· ℕ₊₁→ℤ f)
                                    (sym (ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                                    cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                                    ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                    sym (ℤ.·Assoc (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                                    cong (λ x → e ℤ.· ℕ₊₁→ℤ d ℤ.· x)
                                         (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f)))) ∙
                       sym (ℤ.·DistL+ (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ (b ·₊₁ f))))
                       (ℤ.≤-+o (ℤ.≤-·o ad≤cb)) }

≤-o+ : ∀ m n o →  m ≤ n → o ℚ.+ m ≤ o ℚ.+ n
≤-o+ m n o = recompute≤ ∘ subst2 _≤_ (+Comm m o) (+Comm n o) ∘ ≤-+o m n o

≤Monotone+ : ∀ m n o s → m ≤ n → o ≤ s → m ℚ.+ o ≤ n ℚ.+ s
≤Monotone+ m n o s m≤n o≤s
  = isTrans≤ (m ℚ.+ o)
              (n ℚ.+ o)
              (n ℚ.+ s)
              (≤-+o m n o m≤n)
              (≤-o+ o s n o≤s)

≤-o+-cancel : ∀ m n o →  o ℚ.+ m ≤ o ℚ.+ n → m ≤ n
≤-o+-cancel m n o = recompute≤ ∘
  subst2 _≤_ (+Assoc (- o) o m ∙ cong (ℚ._+ m) (+InvL o) ∙ +IdL m)
             (+Assoc (- o) o n ∙ cong (ℚ._+ n) (+InvL o) ∙ +IdL n) ∘
        ≤-o+ (o ℚ.+ m) (o ℚ.+ n) (- o)

≤-+o-cancel : ∀ m n o → m ℚ.+ o ≤ n ℚ.+ o → m ≤ n
≤-+o-cancel m n o = recompute≤ ∘
    subst2 _≤_ (sym (+Assoc m o (- o)) ∙ cong (λ x → m ℚ.+ x) (+InvR o) ∙ +IdR m)
               (sym (+Assoc n o (- o)) ∙ cong (λ x → n ℚ.+ x) (+InvR o) ∙ +IdR n) ∘
          ≤-+o (m ℚ.+ o) (n ℚ.+ o) (- o)

<-+o : ∀ m n o → m < n → m ℚ.+ o < n ℚ.+ o
<-+o =
  elimProp3 {P = λ a b c → a < b → a ℚ.+ c < b ℚ.+ c}
            (λ x y z → isProp→ (isProp< (x ℚ.+ z) (y ℚ.+ z)))
             λ { (a , b) (c , d) (e , f) (inj ad<cb) →
               inj $ ℤ.recompute< $ subst2 ℤ._<_
                       (cong₂ ℤ._+_
                              (cong (λ x → a ℤ.· ℕ₊₁→ℤ d ℤ.· x)
                                    (ℤ.pos·pos (ℕ₊₁→ℕ f) (ℕ₊₁→ℕ f)) ∙
                                    sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ f)) ∙
                                    cong (a ℤ.·_) (ℤ.·Assoc (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ f) ∙
                                    cong (ℤ._· ℕ₊₁→ℤ f) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                                    sym (ℤ.·Assoc (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))) ∙
                                    ℤ.·Assoc a (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f) ∙
                                    cong (λ x → a ℤ.· ℕ₊₁→ℤ f ℤ.· x)
                                         (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))))
                              (sym (ℤ.·Assoc (e ℤ.· ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                                   cong (λ x → e ℤ.· ℕ₊₁→ℤ b ℤ.· x)
                                        (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f)))) ∙
                       sym (ℤ.·DistL+ (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b) (ℕ₊₁→ℤ (d ·₊₁ f))))
                       (cong₂ ℤ._+_
                              (cong (λ x → c ℤ.· ℕ₊₁→ℤ b ℤ.· x)
                                    (ℤ.pos·pos (ℕ₊₁→ℕ f) (ℕ₊₁→ℕ f)) ∙
                                    sym (ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f ℤ.· ℕ₊₁→ℤ f)) ∙
                                    cong (c ℤ.·_) (ℤ.·Assoc (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ f) ∙
                                    cong (ℤ._· ℕ₊₁→ℤ f) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                                    sym (ℤ.·Assoc (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))) ∙
                                    ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ f) ∙
                                    cong (λ x → c ℤ.· ℕ₊₁→ℤ f ℤ.· x)
                                         (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f))))
                              (cong (ℤ._· ℕ₊₁→ℤ f)
                                    (sym (ℤ.·Assoc e (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                                    cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                                    ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                    sym (ℤ.·Assoc (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                                    cong (λ x → e ℤ.· ℕ₊₁→ℤ d ℤ.· x)
                                         (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f)))) ∙
                       sym (ℤ.·DistL+ (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ (b ·₊₁ f))))
                       (ℤ.<-+o (ℤ.<-·o ad<cb)) }

<-o+ : ∀ m n o → m < n → o ℚ.+ m < o ℚ.+ n
<-o+ m n o = recompute< ∘ subst2 _<_ (+Comm m o) (+Comm n o) ∘ <-+o m n o

<Monotone+ : ∀ m n o s → m < n → o < s → m ℚ.+ o < n ℚ.+ s
<Monotone+ m n o s m<n o<s
  = isTrans< (m ℚ.+ o) (n ℚ.+ o) (n ℚ.+ s) (<-+o m n o m<n) (<-o+ o s n o<s)

<-o+-cancel : ∀ m n o → o ℚ.+ m < o ℚ.+ n → m < n
<-o+-cancel m n o = recompute< ∘
  subst2 _<_ (+Assoc (- o) o m ∙ cong (ℚ._+ m) (+InvL o) ∙ +IdL m)
             (+Assoc (- o) o n ∙ cong (ℚ._+ n) (+InvL o) ∙ +IdL n) ∘
        <-o+ (o ℚ.+ m) (o ℚ.+ n) (- o)

<-+o-cancel : ∀ m n o → m ℚ.+ o < n ℚ.+ o → m < n
<-+o-cancel m n o = recompute< ∘
  subst2 _<_ (sym (+Assoc m o (- o)) ∙ cong (λ x → m ℚ.+ x) (+InvR o) ∙ +IdR m)
             (sym (+Assoc n o (- o)) ∙ cong (λ x → n ℚ.+ x) (+InvR o) ∙ +IdR n) ∘
        <-+o (m ℚ.+ o) (n ℚ.+ o) (- o)

<Weaken≤ : ∀ m n → m < n → m ≤ n
<Weaken≤ m n = elimProp2 {P = λ x y → x < y → x ≤ y}
                             (λ x y → isProp→ (isProp≤ x y))
                             (λ { (a , b) (c , d) → inj ∘ ℤ.<-weaken ∘ _<_.prf }) m n

isTrans<≤ : ∀ m n o → m < n → n ≤ o → m < o
isTrans<≤ =
    elimProp3 {P = λ a b c → a < b → b ≤ c → a < c}
              (λ x _ z → isPropΠ2 λ _ _ → isProp< x z)
               λ { (a , b) (c , d) (e , f) (inj ad<cb) (inj cf≤ed)
                → inj $ ℤ.<-·o-cancel
                 (ℤ.<≤-trans (subst2 ℤ._<_ (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                                            (·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                                            (ℤ.<-·o ad<cb))
                             (subst (_ ℤ.≤_) (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                                    (ℤ.≤-·o cf≤ed)) )}

isTrans≤< : ∀ m n o → m ≤ n → n < o → m < o
isTrans≤< =
    elimProp3 {P = λ a b c → a ≤ b → b < c → a < c}
              (λ x _ z → isPropΠ2 λ _ _ → isProp< x z)
               λ { (a , b) (c , d) (e , f) (inj ad≤cb) (inj cf<ed)
                → inj $ ℤ.<-·o-cancel
                 (ℤ.≤<-trans (subst2 ℤ._≤_ (·CommR a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
                                            (·CommR c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                                            (ℤ.≤-·o ad≤cb))
                             (subst (_ ℤ.<_) (·CommR e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                                    (ℤ.<-·o cf<ed)) )}

≤-·o : ∀ m n o → 0 ≤ o → m ≤ n → m ℚ.· o ≤ n ℚ.· o
≤-·o =
  elimProp3 {P = λ a b c → 0 ≤ c → a ≤ b → a ℚ.· c ≤ b ℚ.· c}
            (λ x y z → isPropΠ2 λ _ _ → isProp≤ (x ℚ.· z) (y ℚ.· z))
             λ { (a , b) (c , d) (e , f) (inj 0≤e) (inj ad≤cb)
             → inj $ ℤ.recompute≤ $
               subst2 ℤ._≤_ (cong (ℤ._· ℕ₊₁→ℤ f) (·CommR a (ℕ₊₁→ℤ d) e) ∙
                              sym (ℤ.·Assoc (a ℤ.· e) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                              cong (a ℤ.· e ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))))
                             (cong (ℤ._· ℕ₊₁→ℤ f) (·CommR c (ℕ₊₁→ℤ b) e) ∙
                              sym (ℤ.·Assoc (c ℤ.· e) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                              cong (c ℤ.· e ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f))))
                             (ℤ.≤-·o (ℤ.0≤o→≤-·o (subst (0 ℤ.≤_) (ℤ.·IdR e) 0≤e) ad≤cb)) }

≤-·o-cancel : ∀ m n o → 0 < o → m ℚ.· o ≤ n ℚ.· o → m ≤ n
≤-·o-cancel =
  elimProp3 {P = λ a b c → 0 < c → a ℚ.· c ≤ b ℚ.· c → a ≤ b}
            (λ x y _ → isPropΠ2 λ _ _ → isProp≤ x y)
             λ { (a , b) (c , d) (e , f) (inj 0<e) (inj aedf≤cebf)
             → inj $ ℤ.0<o→≤-·o-cancel (subst (0 ℤ.<_) (ℤ.·IdR e) 0<e)
               (subst2 ℤ._≤_ (·CommR a e (ℕ₊₁→ℤ d)) (·CommR c e (ℕ₊₁→ℤ b))
                      (ℤ.≤-·o-cancel
                        (subst2 ℤ._≤_ (sym (ℤ.·Assoc a e (ℕ₊₁→ℤ (d ·₊₁ f))) ∙
                                       cong (λ x → a ℤ.· (e ℤ.· x))
                                            (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f)) ∙
                                             assoc {a} {e})
                                       (sym (ℤ.·Assoc c e (ℕ₊₁→ℤ (b ·₊₁ f))) ∙
                                        cong (λ x → c ℤ.· (e ℤ.· x))
                                             (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f)) ∙
                                              assoc {c} {e})
                                        aedf≤cebf))) }

  where assoc : ∀{a b c d} → a ℤ.· (b ℤ.· (c ℤ.· d)) ≡ a ℤ.· b ℤ.· c ℤ.· d
        assoc {a} {b} {c} {d} = cong (a ℤ.·_) (ℤ.·Assoc b c d) ∙
                                ℤ.·Assoc a (b ℤ.· c) d ∙
                                cong (ℤ._· d) (ℤ.·Assoc a b c)

<-·o : ∀ m n o → 0 < o → m < n → m ℚ.· o < n ℚ.· o
<-·o =
  elimProp3 {P = λ a b c → 0 < c → a < b → a ℚ.· c < b ℚ.· c}
            (λ x y z → isPropΠ2 λ _ _ → isProp< (x ℚ.· z) (y ℚ.· z))
             λ { (a , b) (c , d) (e , f) (inj 0<e) (inj ad<cb)
             → inj $ ℤ.recompute< $
               subst2 ℤ._<_ (cong (ℤ._· ℕ₊₁→ℤ f) (·CommR a (ℕ₊₁→ℤ d) e) ∙
                             sym (ℤ.·Assoc (a ℤ.· e) (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f)) ∙
                             cong (a ℤ.· e ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))))
                            (cong (ℤ._· ℕ₊₁→ℤ f) (·CommR c (ℕ₊₁→ℤ b) e) ∙
                             sym (ℤ.·Assoc (c ℤ.· e) (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f)) ∙
                             cong (c ℤ.· e ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f))))
                            (ℤ.<-·o (ℤ.0<o→<-·o (subst (0 ℤ.<_) (ℤ.·IdR e) 0<e) ad<cb)) }

<-·o-cancel : ∀ m n o → 0 < o → m ℚ.· o < n ℚ.· o → m < n
<-·o-cancel =
  elimProp3 {P = λ a b c → 0 < c → a ℚ.· c < b ℚ.· c → a < b}
            (λ x y _ → isPropΠ2 λ _ _ → isProp< x y)
             λ { (a , b) (c , d) (e , f) (inj 0<e) (inj aedf<cebf)
             → inj $ ℤ.0<o→<-·o-cancel (subst (0 ℤ.<_) (ℤ.·IdR e) 0<e)
               (subst2 ℤ._<_ (·CommR a e (ℕ₊₁→ℤ d)) (·CommR c e (ℕ₊₁→ℤ b))
                      (ℤ.<-·o-cancel
                        (subst2 ℤ._<_ (sym (ℤ.·Assoc a e (ℕ₊₁→ℤ (d ·₊₁ f))) ∙
                                       cong (λ x → a ℤ.· (e ℤ.· x))
                                            (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f)) ∙
                                             assoc {a} {e})
                                       (sym (ℤ.·Assoc c e (ℕ₊₁→ℤ (b ·₊₁ f))) ∙
                                        cong (λ x → c ℤ.· (e ℤ.· x))
                                             (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ f)) ∙
                                              assoc {c} {e})
                                        aedf<cebf))) }

  where assoc : ∀{a b c d} → a ℤ.· (b ℤ.· (c ℤ.· d)) ≡ a ℤ.· b ℤ.· c ℤ.· d
        assoc {a} {b} {c} {d} = cong (a ℤ.·_) (ℤ.·Assoc b c d) ∙
                                ℤ.·Assoc a (b ℤ.· c) d ∙
                                cong (ℤ._· d) (ℤ.·Assoc a b c)

min≤ : ∀ m n → ℚ.min m n ≤ m
min≤
    = elimProp2 {P = λ a b → ℚ.min a b ≤ a}
                (λ x y → isProp≤ (ℚ.min x y) x)
                 λ { (a , b) (c , d)
                  → inj (ℤ.recompute≤ (
                    subst2 ℤ._≤_ (sym (ℤ.·DistPosLMin (a ℤ.· ℕ₊₁→ℤ d)
                                                       (c ℤ.· ℕ₊₁→ℤ b)
                                                       (ℕ₊₁→ℕ b)))
                                  (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                   cong (a ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                                  cong ℕ₊₁→ℤ (·₊₁-comm d b)))
                                  ℤ.min≤)) }

≤→min : ∀ m n → m ≤ n → ℚ.min m n ≡ m
≤→min
    = elimProp2 {P = λ a b → a ≤ b → ℚ.min a b ≡ a}
                (λ x y → isProp→ (isSetℚ (ℚ.min x y) x))
                 λ { (a , b) (c , d) (inj ad≤cb)
                  → eq/ (ℤ.min (a ℤ.· ℕ₊₁→ℤ d)
                               (c ℤ.· ℕ₊₁→ℤ b)
                         , b ·₊₁ d)
                        (a , b)
                        (cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.≤→min ad≤cb) ∙
                         sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                         cong (a ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                        cong ℕ₊₁→ℤ (·₊₁-comm d b))) }

≤max : ∀ m n → m ≤ ℚ.max m n
≤max
    = elimProp2 {P = λ a b → a ≤ ℚ.max a b}
                (λ x y → isProp≤ x (ℚ.max x y))
                 λ { (a , b) (c , d)
                  → inj (ℤ.recompute≤ (
                    subst2 ℤ._≤_ (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                   cong (a ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                                  cong ℕ₊₁→ℤ (·₊₁-comm d b)))
                                  (sym (ℤ.·DistPosLMax (a ℤ.· ℕ₊₁→ℤ d)
                                                       (c ℤ.· ℕ₊₁→ℤ b)
                                                       (ℕ₊₁→ℕ b)))
                                  ℤ.≤max)) }

≤→max : ∀ m n →  m ≤ n → ℚ.max m n ≡ n
≤→max m n
    = elimProp2 {P = λ a b → a ≤ b → ℚ.max a b ≡ b}
                (λ x y → isProp→ (isSetℚ (ℚ.max x y) y))
                (λ { (a , b) (c , d) (inj ad≤cb)
                  → eq/ (ℤ.max (a ℤ.· ℕ₊₁→ℤ d)
                               (c ℤ.· ℕ₊₁→ℤ b)
                         , b ·₊₁ d)
                        (c , d)
                        (cong (ℤ._· ℕ₊₁→ℤ d) (ℤ.≤→max ad≤cb) ∙
                         sym (ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ d)) ∙
                         cong (c ℤ.·_) (sym (ℤ.pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d)))) }) m n

≤Dec : ∀ m n → Dec (m ≤ n)
≤Dec = elimProp2 (λ x y → isPropDec (isProp≤ x y))
       (λ (a , b) (c , d) → decRec (yes ∘ inj) (no ∘ _∘ _≤_.prf)
        (ℤ.≤Dec (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b))  )

<Dec : ∀ m n → Dec (m < n)
<Dec = elimProp2 (λ x y → isPropDec (isProp< x y))
       λ { (a , b) (c , d) → decRec (yes ∘ inj) (no ∘ _∘ _<_.prf)
        (ℤ.<Dec (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)) }


_≟_ : (m n : ℚ) → Trichotomy m n
m ≟ n with discreteℚ m n
... | yes m≡n = eq m≡n
... | no m≢n with inequalityImplies# m n m≢n
...             | inl m<n = lt m<n
...             | inr n<m = gt n<m

≤MonotoneMin : ∀ m n o s → m ≤ n → o ≤ s → ℚ.min m o ≤ ℚ.min n s
≤MonotoneMin m n o s m≤n o≤s = recompute≤ $
  subst (_≤ ℚ.min n s)
        (sym (ℚ.minAssoc n s (ℚ.min m o)) ∙
         cong (ℚ.min n) (ℚ.minAssoc s m o ∙
                         cong (λ a → ℚ.min a o) (ℚ.minComm s m) ∙
                               sym (ℚ.minAssoc m s o)) ∙
                         ℚ.minAssoc n m (ℚ.min s o) ∙
         cong₂ ℚ.min (ℚ.minComm n m ∙ ≤→min m n m≤n)
                     (ℚ.minComm s o ∙ ≤→min o s o≤s))
         (min≤ (ℚ.min n s) (ℚ.min m o))

≤MonotoneMax : ∀ m n o s → m ≤ n → o ≤ s → ℚ.max m o ≤ ℚ.max n s
≤MonotoneMax m n o s m≤n o≤s = recompute≤ $
  subst (ℚ.max m o ≤_)
        (sym (ℚ.maxAssoc m o (ℚ.max n s)) ∙
         cong (ℚ.max m) (ℚ.maxAssoc o n s ∙
                         cong (λ a → ℚ.max a s) (ℚ.maxComm o n) ∙
                               sym (ℚ.maxAssoc n o s)) ∙
                         ℚ.maxAssoc m n (ℚ.max o s) ∙
         cong₂ ℚ.max (≤→max m n m≤n) (≤→max o s o≤s))
        (≤max (ℚ.max m o) (ℚ.max n s))

≡Weaken≤ : ∀ m n → m ≡ n → m ≤ n
≡Weaken≤ m n m≡n = recompute≤ $ subst (m ≤_) m≡n (isRefl≤ m)

≤→≯ : ∀ m n →  m ≤ n → ¬ (m > n)
≤→≯ m n m≤n = recompute¬< $
  λ n<m → isIrrefl< n (subst (n <_) (isAntisym≤ m n m≤n (<Weaken≤ n m n<m)) n<m)

≮→≥ : ∀ m n → ¬ (m < n) → m ≥ n
≮→≥ m n m≮n with discreteℚ m n
... | yes m≡n = ≡Weaken≤ n m (sym m≡n)
... | no  m≢n = ∥₁.elim (λ _ → isProp≤ n m)
                        (⊎.rec (⊥.rec ∘ m≮n) (<Weaken≤ n m))
                         ∣ inequalityImplies# m n m≢n ∣₁

0<+ : ∀ m n → 0 < m ℚ.+ n → (0 < m) ⊎ (0 < n)
0<+ m n 0<m+n with <Dec 0 m | <Dec 0 n
... | no 0≮m | no 0≮n = ⊥.rec (≤→≯ (m ℚ.+ n) 0 (≤Monotone+ m 0 n 0 (≮→≥ 0 m 0≮m) (≮→≥ 0 n 0≮n)) 0<m+n)
... | no _    | yes 0<n = inr 0<n
... | yes 0<m | _ = inl 0<m

<ℤ→<ℚ : ∀ m n k → m ℤ.< n → [ m / k ] < [ n / k ]
<ℤ→<ℚ m n (1+ k) m<n = inj (ℤ.<-·o {m} m<n)
