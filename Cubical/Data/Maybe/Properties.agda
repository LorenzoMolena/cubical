module Cubical.Data.Maybe.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_; idfun)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed.Base using (Pointed; _→∙_; pt)
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Functions.Embedding using (isEmbedding)

open import Cubical.Data.Empty as ⊥ using (⊥; isProp⊥)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (ΣPathP)

open import Cubical.Relation.Nullary using (¬_; Discrete; yes; no)

open import Cubical.Data.Maybe.Base as Maybe

Maybe∙ : ∀ {ℓ} (A : Type ℓ) → Pointed ℓ
Maybe∙ A .fst = Maybe A
Maybe∙ A .snd = nothing

-- Maybe∙ is the "free pointing" functor, that is, left adjoint to the
-- forgetful functor forgetting the base point.
module _ {ℓ} (A : Type ℓ) {ℓ'} (B : Pointed ℓ') where

  freelyPointedIso : Iso (Maybe∙ A →∙ B) (A → ⟨ B ⟩)
  Iso.fun freelyPointedIso f∙ = fst f∙ ∘ just
  Iso.inv freelyPointedIso f = Maybe.rec (pt B) f , refl
  Iso.sec freelyPointedIso f = refl
  Iso.ret freelyPointedIso f∙ =
    ΣPathP
      ( funExt (Maybe.elim _ (sym (snd f∙)) (λ a → refl))
      , λ i j → snd f∙ (~ i ∨ j))

map-Maybe-id : ∀ {ℓ} {A : Type ℓ} → ∀ m → map-Maybe (idfun A) m ≡ m
map-Maybe-id nothing = refl
map-Maybe-id (just _) = refl

-- Path space of Maybe type
module MaybePath {ℓ} {A : Type ℓ} where
  Cover : Maybe A → Maybe A → Type ℓ
  Cover nothing  nothing   = Lift Unit
  Cover nothing  (just _)  = Lift ⊥
  Cover (just _) nothing   = Lift ⊥
  Cover (just a) (just a') = a ≡ a'

  reflCode : (c : Maybe A) → Cover c c
  reflCode nothing  = lift tt
  reflCode (just b) = refl

  encode : ∀ c c' → c ≡ c' → Cover c c'
  encode c _ = J (λ c' _ → Cover c c') (reflCode c)

  encodeRefl : ∀ c → encode c c refl ≡ reflCode c
  encodeRefl c = JRefl (λ c' _ → Cover c c') (reflCode c)

  decode : ∀ c c' → Cover c c' → c ≡ c'
  decode nothing  nothing  _ = refl
  decode (just _) (just _) p = cong just p

  decodeRefl : ∀ c → decode c c (reflCode c) ≡ refl
  decodeRefl nothing  = refl
  decodeRefl (just _) = refl

  decodeEncode : ∀ c c' → (p : c ≡ c') → decode c c' (encode c c' p) ≡ p
  decodeEncode c _ =
    J (λ c' p → decode c c' (encode c c' p) ≡ p)
      (cong (decode c c) (encodeRefl c) ∙ decodeRefl c)

  encodeDecode : ∀ c c' → (d : Cover c c') → encode c c' (decode c c' d) ≡ d
  encodeDecode nothing nothing _ = refl
  encodeDecode (just a) (just a') =
    J (λ a' p → encode (just a) (just a') (cong just p) ≡ p) (encodeRefl (just a))

  Cover≃Path : ∀ c c' → Cover c c' ≃ (c ≡ c')
  Cover≃Path c c' = isoToEquiv
    (iso (decode c c') (encode c c') (decodeEncode c c') (encodeDecode c c'))

  Cover≡Path : ∀ c c' → Cover c c' ≡ (c ≡ c')
  Cover≡Path c c' = isoToPath
    (iso (decode c c') (encode c c') (decodeEncode c c') (encodeDecode c c'))

  isOfHLevelCover : (n : HLevel)
    → isOfHLevel (suc (suc n)) A
    → ∀ c c' → isOfHLevel (suc n) (Cover c c')
  isOfHLevelCover n p nothing  nothing   = isOfHLevelLift (suc n) (isOfHLevelUnit (suc n))
  isOfHLevelCover n p nothing  (just a') = isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (just a) nothing   = isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (just a) (just a') = p a a'

isOfHLevelMaybe : ∀ {ℓ} (n : HLevel) {A : Type ℓ}
  → isOfHLevel (suc (suc n)) A
  → isOfHLevel (suc (suc n)) (Maybe A)
isOfHLevelMaybe n lA c c' =
  isOfHLevelRetract (suc n)
    (MaybePath.encode c c')
    (MaybePath.decode c c')
    (MaybePath.decodeEncode c c')
    (MaybePath.isOfHLevelCover n lA c c')

private
 variable
   ℓ : Level
   A : Type ℓ

fromJust-def : A → Maybe A → A
fromJust-def a nothing = a
fromJust-def _ (just a) = a

just-inj : (x y : A) → just x ≡ just y → x ≡ y
just-inj x _ eq = cong (fromJust-def x) eq

isEmbedding-just : isEmbedding (just {A = A})
isEmbedding-just  w z = MaybePath.Cover≃Path (just w) (just z) .snd

¬nothing≡just : ∀ {x : A} → ¬ (nothing ≡ just x)
¬nothing≡just {A = A} {x = x} p = lower (subst (caseMaybe (Maybe A) (Lift ⊥)) p (just x))

¬just≡nothing : ∀ {x : A} → ¬ (just x ≡ nothing)
¬just≡nothing {A = A} {x = x} p = lower (subst (caseMaybe (Lift ⊥) (Maybe A)) p (just x))

isProp-x≡nothing : (x : Maybe A) → isProp (x ≡ nothing)
isProp-x≡nothing nothing x w =
  subst isProp (MaybePath.Cover≡Path nothing nothing) (isOfHLevelLift 1 isPropUnit) x w
isProp-x≡nothing (just _) p _ = ⊥.rec (¬just≡nothing p)

isProp-nothing≡x : (x : Maybe A) → isProp (nothing ≡ x)
isProp-nothing≡x nothing x w =
  subst isProp (MaybePath.Cover≡Path nothing nothing) (isOfHLevelLift 1 isPropUnit) x w
isProp-nothing≡x (just _) p _ = ⊥.rec (¬nothing≡just p)

isContr-nothing≡nothing : isContr (nothing {A = A} ≡ nothing)
isContr-nothing≡nothing = inhProp→isContr refl (isProp-x≡nothing _)

discreteMaybe : Discrete A → Discrete (Maybe A)
discreteMaybe eqA nothing nothing    = yes refl
discreteMaybe eqA nothing (just a')  = no ¬nothing≡just
discreteMaybe eqA (just a) nothing   = no ¬just≡nothing
discreteMaybe eqA (just a) (just a') with eqA a a'
... | yes p = yes (cong just p)
... | no ¬p = no (λ p → ¬p (just-inj _ _ p))

module SumUnit where
  Maybe→SumUnit : Maybe A → Unit ⊎ A
  Maybe→SumUnit nothing  = inl tt
  Maybe→SumUnit (just a) = inr a

  SumUnit→Maybe : Unit ⊎ A → Maybe A
  SumUnit→Maybe (inl _) = nothing
  SumUnit→Maybe (inr a) = just a

  Maybe→SumUnit→Maybe : (x : Maybe A) → SumUnit→Maybe (Maybe→SumUnit x) ≡ x
  Maybe→SumUnit→Maybe nothing  = refl
  Maybe→SumUnit→Maybe (just _) = refl

  SumUnit→Maybe→SumUnit : (x : Unit ⊎ A) → Maybe→SumUnit (SumUnit→Maybe x) ≡ x
  SumUnit→Maybe→SumUnit (inl _) = refl
  SumUnit→Maybe→SumUnit (inr _) = refl

Maybe≡SumUnit : Maybe A ≡ Unit ⊎ A
Maybe≡SumUnit = isoToPath (iso Maybe→SumUnit SumUnit→Maybe SumUnit→Maybe→SumUnit Maybe→SumUnit→Maybe)
  where open SumUnit

congMaybeEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → A ≃ B → Maybe A ≃ Maybe B
congMaybeEquiv e = isoToEquiv isom
  where
  open Iso
  isom : Iso _ _
  isom .fun = map-Maybe (equivFun e)
  isom .inv = map-Maybe (invEq e)
  isom .sec nothing = refl
  isom .sec (just b) = cong just (secEq e b)
  isom .ret nothing = refl
  isom .ret (just a) = cong just (retEq e a)

infixl 20 _⁇→_ 

_⁇→_ : ∀ {ℓ'} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ') 
A ⁇→ B = (mbA : Maybe A) → caseMaybe Unit* B mbA

⁇λ_ : ∀ {ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → A ⁇→ B
⁇λ_ f nothing = tt*
⁇λ_ f (just a) = f a

∘rec : ∀ {ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : B → C) n j
           (x : Maybe A) → f (Maybe.rec n j x) ≡ Maybe.rec (f n) (f ∘ j) x
∘rec f n j nothing = refl
∘rec f n j (just x) = refl

∘fromJust-def : ∀ {ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) n
           (x : Maybe A) → f (fromJust-def n x) ≡ fromJust-def (f n) (map-Maybe f x)
∘fromJust-def f n nothing = refl
∘fromJust-def f n (just x) = refl
