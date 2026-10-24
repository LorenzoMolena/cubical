{-# OPTIONS --safe #-}

module HeytingField.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset using (ℙ; _∈_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat as ℕ using (ℕ) hiding (module ℕ)
open import Cubical.Data.FinData using (FinVec; Fin; ¬Fin0; zero; suc; one)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary

open import Cubical.Data.Sigma

open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing

open import HeytingField.Base

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  F G H : HeytingField ℓ ℓ'

module FieldTheory ((R , F) : HeytingField ℓ ℓ') where
  open HeytingFieldStr F public
  open Sum (HeytingField→Ring (R , F))
  FCRing = HeytingField→CommRing (R , F)
  open CommRingTheory FCRing public
  FRing = HeytingField→Ring (R , F)
  open RingTheory FRing public
  open Units FCRing

  private variable
    x y : R

  #→≢ : ∀ x y → x # y → ¬ x ≡ y
  #→≢ x y x#y x≡y = is-irrefl y $ subst (_# y) x≡y x#y

  FieldIsSeparated : Separated R
  FieldIsSeparated x y ¬¬x≡y = isTight x y λ x#y → ¬¬x≡y $ #→≢ x y x#y

  contrapos#→≡ : ∀ x y z w → (x # y → z # w) → z ≡ w → x ≡ y
  contrapos#→≡ x y z w x#y→z#w z≡w = isTight x y λ x#y → #→≢ z w (x#y→z#w x#y) z≡w

  FieldIsNonTrivial : 1r # 0r
  FieldIsNonTrivial = IsInv→#0 1r 1r (·IdR 1r)

  +Respect#ₗ : ∀ x y z → x # y → (z + x) # (z + y)
  +Respect#ₗ x y z x#y = subst2 _#_ (+Comm _ _) (+Comm _ _) (+Respect#ᵣ x y z x#y)

  -- x # y is the same as invertibility of x - y
  -- However, in the definition I chose to let the user give a custom implementation of # for two reasons:
  -- It's sometimes more convenient, for example in an ordered field where we can define x # y to be x < y or y < x
  -- I also allow it to have a smaller universe level, which is useful when implementing e.g. the Dedekind reals predicatively
  #→DiffIsInv : ∀ x y → x # y → (x - y) ∈ FCRing ˣ
  #→DiffIsInv x y x#y = #0→IsInv (x - y) (subst (_ #_) (+InvR y) (+Respect#ᵣ x y (- y) x#y))

  DiffIsInv→# : ∀ x y → (x - y) ∈ FCRing ˣ → x # y
  DiffIsInv→# x y (x-y⁻¹ , p) = subst2 _#_ (solve! FCRing) (+IdL y) (+Respect#ᵣ _ _ y (IsInv→#0 _ x-y⁻¹ p))

  ·Respect#ᵣ : ∀ x y z → z # 0r → x # y → (x · z) # (y · z)
  ·Respect#ᵣ x y z z#0 x#y = DiffIsInv→# _ _ $ subst (_∈ (FCRing ˣ)) (solve! FCRing) $
    RˣMultClosed _ _ ⦃ #→DiffIsInv _ _ x#y ⦄ ⦃ #0→IsInv _ z#0 ⦄

  ·Respect#ₗ : ∀ x y z → z # 0r → x # y → (z · x) # (z · y)
  ·Respect#ₗ x y z z#0 x#y = subst2 _#_ (·Comm _ _) (·Comm _ _) (·Respect#ᵣ x y z z#0 x#y)

  +Cancel#ᵣ : ∀ x y z → (x + z) # (y + z) → x # y
  +Cancel#ᵣ x y z x+z#y+z = subst2 _#_ (solve! FCRing) (solve! FCRing) (+Respect#ᵣ _ _ (- z) x+z#y+z)

  +Cancel#ₗ : ∀ x y z → (z + x) # (z + y) → x # y
  +Cancel#ₗ x y z z+x#z+y = +Cancel#ᵣ x y z (subst2 _#_ (+Comm _ _) (+Comm _ _) z+x#z+y)

  recipRespect# : ∀ z (z#0 : z # 0r) → recip z z#0 # 0r
  recipRespect# z z#0 = IsInv→#0 _ z (isLInvRecip z z#0)

  ·Cancel#ᵣ : ∀ x y z → (x · z) # (y · z) → x # y
  ·Cancel#ᵣ x y z xz#yz with #→DiffIsInv _ _ xz#yz
  ... | (xz-yz⁻¹ , p) = DiffIsInv→# _ _ (z · xz-yz⁻¹ , solve! FCRing ∙ p)

  ·Cancel#ₗ : ∀ x y z → (z · x) # (z · y) → x # y
  ·Cancel#ₗ x y z zx#zy = ·Cancel#ᵣ x y z (subst2 _#_ (·Comm _ _) (·Comm _ _) zx#zy)

  ·Cancelᵣ : ∀ x y z → z # 0r → x · z ≡ y · z → x ≡ y
  ·Cancelᵣ x y z z#0 = contrapos#→≡ _ _ _ _ (·Respect#ᵣ x y z z#0)

  ·Cancelₗ : ∀ x y z → z # 0r → z · x ≡ z · y → x ≡ y
  ·Cancelₗ x y z z#0 = contrapos#→≡ _ _ _ _ (·Respect#ₗ x y z z#0)

  recip-eq-elim : ∀ x y z z#0 → x ≡ z · y → x · recip z z#0 ≡ y
  recip-eq-elim x y z z#0 x≡zy = congL _·_ (x≡zy ∙ ·Comm z y) ∙ sym (·Assoc _ _ _) ∙ congR _·_ (isRInvRecip z z#0) ∙ ·IdR y

  recip≡ : ∀ x y x#0 → x · y ≡ 1r → recip x x#0 ≡ y
  recip≡ x y x#0 xy≡1 = cong fst (inverseUniqueness x (#0→IsInv x x#0) (y , xy≡1))

  recip-1 : ∀ 1#0 → recip 1r 1#0 ≡ 1r
  recip-1 1#0 = recip≡ _ _ _ (·IdR 1r)

  cross-multiply : ∀ x y z w z#0 w#0 → z · y ≡ w · x → x · recip z z#0 ≡ y · recip w w#0
  cross-multiply x y z w z#0 w#0 zy≡wx = recip-eq-elim _ _ _ z#0 (sym (·Assoc _ _ _ ∙ recip-eq-elim _ _ _ w#0 zy≡wx))

  FieldIs#BinSumLocal : ∀ x y → (x + y) # 0r → ∥ (x # 0r) ⊎ (y # 0r) ∥₁
  FieldIs#BinSumLocal x y x+y#0 = PT.map (
      ⊎.map (idfun _) λ -y#0 → is-sym _ _ (subst2 _#_ (+InvL y) (+IdL y) (+Respect#ᵣ _ _ y -y#0))
    ) (is-cotrans x (- y) 0r (subst2 _#_ (solve! FCRing) (solve! FCRing) (+Respect#ᵣ _ _ (- y) x+y#0)))

  FieldIsBinSumLocal : Characterizations.BinSum.BinSum FCRing
  FieldIsBinSumLocal x y x+y⁻¹ = PT.map (⊎.map (#0→IsInv x) (#0→IsInv y)) (FieldIs#BinSumLocal x y (IsInv→#0' _ x+y⁻¹))

  FieldIsLocal : isLocal FCRing
  FieldIsLocal = Characterizations.BinSum.alternative→isLocal FCRing (#→≢ _ _ FieldIsNonTrivial , FieldIsBinSumLocal)

  FieldIs#Local : {n : ℕ} → (xs : FinVec R n) → (∑ xs) # 0r → ∃[ i ∈ Fin n ] (xs i # 0r)
  FieldIs#Local xs ∑xs#0 = PT.map (map-snd (IsInv→#0' _)) (FieldIsLocal xs (#0→IsInv _ ∑xs#0))

-- Any homomorphism of rings automatically preserves the apartness
module _ ((A , F) : HeytingField ℓ ℓ'') ((B , G) : HeytingField ℓ' ℓ''')
         (f : A → B) (fIsRingHom : IsRingHom (HeytingFieldStr→RingStr F) f (HeytingFieldStr→RingStr G)) where
  private
    module F = FieldTheory (A , F)
    module G = FieldTheory (B , G)

  RingHomOfFieldsPres# : ∀ x y → x F.# y → f x G.# f y
  RingHomOfFieldsPres# x y x#y = let (x-y⁻¹ , p) = F.#→DiffIsInv _ _ x#y in G.DiffIsInv→# _ _ $
    f x-y⁻¹ , sym (pres· _ _ ∙∙ congL G._·_ (pres+ _ _) ∙∙ congL G._·_ (congR G._+_ (pres- _))) ∙∙ cong f p ∙∙ pres1
    where open IsRingHom fIsRingHom

  RingHomOfFieldsIsInj : ∀ x y → f x ≡ f y → x ≡ y
  RingHomOfFieldsIsInj x y fx≡fy = F.isTight _ _ λ x#y → G.#→≢ (f x) (f y) (RingHomOfFieldsPres# x y x#y) fx≡fy

  module _ (strongExt : ∀ x y → f x G.# f y → x F.# y) where
    open IsHeytingFieldHom
    open IsRingHom

    strongExtRingHomIsFieldHom : IsHeytingFieldHom F f G
    strongExtRingHomIsFieldHom = λ where
      .pres0 → fIsRingHom .pres0
      .pres1 → fIsRingHom .pres1
      .pres+ → fIsRingHom .pres+
      .pres· → fIsRingHom .pres·
      .pres- → fIsRingHom .pres-
      .pres# x y → propBiimpl→Equiv (F.is-prop-valued _ _) (G.is-prop-valued _ _) (RingHomOfFieldsPres# x y) (strongExt x y)

module _ {F : HeytingField ℓ ℓ''} {G : HeytingField ℓ' ℓ'''} (f : HeytingFieldHom F G) where
  FieldHomIsInj : ∀ x y → f .fst x ≡ f .fst y → x ≡ y
  FieldHomIsInj = RingHomOfFieldsIsInj F G (f .fst) (isHeytingFieldHom→isRingHom (F .snd) _ (G .snd) (f .snd))

-- We can make a smart constructor for field homomorphisms, as they are just strongly extensional ring homomorphisms
module _ {A : Type ℓ} {B : Type ℓ'} {F : HeytingFieldStr ℓ'' A} {G : HeytingFieldStr ℓ''' B} {f : A → B} where
  private
    module F = FieldTheory (A , F)
    module G = FieldTheory (B , G)

  module _ (pres+ : ∀ x y → f (x F.+ y) ≡ f x G.+ f y) (pres1 : f F.1r ≡ G.1r)
           (pres· : ∀ x y → f (x F.· y) ≡ f x G.· f y) (strongExt : ∀ x y → f x G.# f y → x F.# y) where

    makeIsFieldHom : IsHeytingFieldHom F f G
    makeIsFieldHom = strongExtRingHomIsFieldHom _ _ f (makeIsRingHom pres1 pres+ pres·) strongExt

module _ {F : HeytingField ℓ ℓ''} {G : HeytingField ℓ' ℓ'''} (f : ⟨ F ⟩ → ⟨ G ⟩) where
  private
    module F = FieldTheory F
    module G = FieldTheory G

  module _ (pres+ : ∀ x y → f (x F.+ y) ≡ f x G.+ f y) (pres1 : f F.1r ≡ G.1r)
           (pres· : ∀ x y → f (x F.· y) ≡ f x G.· f y) (strongExt : ∀ x y → f x G.# f y → x F.# y) where

    makeFieldHom : HeytingFieldHom F G
    makeFieldHom = f , makeIsFieldHom pres+ pres1 pres· strongExt

-- Although not every ring homomorphism is a field homomorphism, every ring equivalence is an equivalence of fields:
module _ {A : Type ℓ} {B : Type ℓ'} {F : HeytingFieldStr ℓ'' A} (e : A ≃ B) {G : HeytingFieldStr ℓ''' B}
         (eIsRingEquiv : IsRingEquiv (HeytingFieldStr→RingStr F) e (HeytingFieldStr→RingStr G)) where
  private
    module F = FieldTheory (A , F)
    module G = FieldTheory (B , G)

  ringEquivIsStrongExt : ∀ x y → e .fst x G.# e .fst y → x F.# y
  ringEquivIsStrongExt x y ex#ey = subst2 F._#_ (retEq e x) (retEq e y) $
    RingHomOfFieldsPres# (B , G) (A , F) (invEq e) (isRingHomInv (e , eIsRingEquiv)) _ _ ex#ey
    where open RingEquivs

  ringEquivIsFieldEquiv : IsHeytingFieldEquiv F e G
  ringEquivIsFieldEquiv = strongExtRingHomIsFieldHom _ _ _ eIsRingEquiv ringEquivIsStrongExt

module _ {F : HeytingField ℓ ℓ''} {G : HeytingField ℓ' ℓ'''} where
  RingEquiv→FieldEquiv : RingEquiv (HeytingField→Ring F) (HeytingField→Ring G) → HeytingFieldEquiv F G
  RingEquiv→FieldEquiv (e , eIsHom) = e , ringEquivIsFieldEquiv e eIsHom

  FieldEquiv≃RingEquiv : HeytingFieldEquiv F G ≃ RingEquiv (HeytingField→Ring F) (HeytingField→Ring G)
  FieldEquiv≃RingEquiv = Σ-cong-equiv-snd λ e →
    propBiimpl→Equiv (isPropIsHeytingFieldHom _ _ _) (isPropIsRingHom _ _ _)
                     (isHeytingFieldHom→isRingHom _ _ _) (ringEquivIsFieldEquiv e)

  isEquivHeytingFieldEquiv→RingEquiv : isEquiv (HeytingFieldEquiv→RingEquiv F G)
  isEquivHeytingFieldEquiv→RingEquiv = FieldEquiv≃RingEquiv .snd

  FieldEquiv≡ : {f g : HeytingFieldEquiv F G} → f .fst .fst ≡ g .fst .fst → f ≡ g
  FieldEquiv≡ = Σ≡Prop (λ _ → isPropIsHeytingFieldHom _ _ _) ∘ Σ≡Prop (λ _ → isPropIsEquiv _)

open RingHoms
open IsHeytingFieldHom

idFieldHom : HeytingFieldHom F F
idFieldHom = _ , strongExtRingHomIsFieldHom _ _ _ (idRingHom _ .snd) λ _ _ → idfun _

compFieldHom : HeytingFieldHom F G → HeytingFieldHom G H → HeytingFieldHom F H
compFieldHom f g = _ , strongExtRingHomIsFieldHom _ _ _
  (compIsRingHom (HeytingFieldHom→RingHom _ _ g .snd) (HeytingFieldHom→RingHom _ _ f .snd)) λ x y x#y →
    invEq (f .snd .pres# _ _) (invEq (g .snd .pres# _ _) x#y)

open RingEquivs

idFieldEquiv : HeytingFieldEquiv F F
idFieldEquiv = RingEquiv→FieldEquiv (idRingEquiv _)

compFieldEquiv : HeytingFieldEquiv F G → HeytingFieldEquiv G H → HeytingFieldEquiv F H
compFieldEquiv f g = RingEquiv→FieldEquiv $ compRingEquiv
  (HeytingFieldEquiv→RingEquiv _ _ f) (HeytingFieldEquiv→RingEquiv _ _ g)

invFieldEquiv : HeytingFieldEquiv F G → HeytingFieldEquiv G F
invFieldEquiv f = RingEquiv→FieldEquiv (invRingEquiv (HeytingFieldEquiv→RingEquiv _ _ f))

-- Discrete (Geometric) fields
module _ (F : HeytingField ℓ ℓ') where
  open FieldTheory F

  isDiscField : Type _
  isDiscField = ∀ x y → Dec (x # y)

  -- The underlying set of a Geometric field is discrete
  isDiscField→isDisc : isDiscField → Discrete ⟨ F ⟩
  isDiscField→isDisc FDisc x y with FDisc x y
  ... | yes x#y = no (#→≢ x y x#y)
  ... | no ¬x#y = yes (isTight x y ¬x#y)
