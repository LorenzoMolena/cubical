open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Elim {ℓ} {ℓ'}
  (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

private
  M = M' .fst
  open PremetricStr (M' .snd)
  open import Cubical.Relation.Premetric.Completion.Base M' renaming (ℭ to ℭM)

record Elimℭ
  {ℓA} {ℓB} (A : ℭM → Type ℓA)
  (B : ∀ {x y : ℭM} → A x → A y → ∀ ε → x ∼[ ε ] y → Type ℓB)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA        : ∀ x → A (ι x)
    limA      : ∀ x xc → (a∘x : ∀ q → A (x q))
                → (∀ ε δ → B {x ε} {x δ} (a∘x ε) (a∘x δ) (ε +₊ δ) (xc ε δ))
                → A (lim x xc)
    eqA       : ∀ {x y} p a a' → (∀ ε δ → B a a' _ (p (ε +₊ δ)))
                → (∀ ε → B a a' ε (p ε))
                → PathP (λ i → A (eqℭ x y p i)) a a'
    ι-ι-B     : ∀ x y ε x≈y → B (ιA x) (ιA y) ε (ι-ι x y ε x≈y)
    ι-lim-B   : ∀ x y ε δ yc Δ r a∘y ydc
                → B (ιA x) (a∘y δ) (ε -₊ δ , Δ) r
                → B (ιA x) (limA y yc a∘y ydc) ε (ι-lim x y ε δ yc Δ r)
    lim-ι-B   : ∀ x y ε δ xc Δ u a∘x xdc
                → B (a∘x δ) (ιA y) (ε -₊ δ , Δ) u
                → B (limA x xc a∘x xdc) (ιA y) ε (lim-ι x y ε δ xc Δ u)
    lim-lim-B : ∀ x y ε δ η xc yc Δ
                → (r : x δ ∼[ ε -₊ (δ +₊ η) , Δ ] y η)
                → ∀ a∘x xdc a∘y ydc
                → B (a∘x δ) (a∘y η) (ε -₊ (δ +₊ η) , Δ) r
                → B (limA x xc a∘x xdc) (limA y yc a∘y ydc) ε
                    (lim-lim x y ε δ η xc yc Δ r)
    isPropB   : ∀ {x y} a a' ε u → isProp (B {x} {y} a a' ε u)

  go : ∀ x → A x
  go∼ : ∀ {x x' ε} → (r : x ∼[ ε ] x') → B (go x) (go x') ε r

  go (ι x)           = ιA x
  go (lim x xc)      = limA x xc (go ∘ x) λ ε δ → go∼ (xc ε δ)
  go (eqℭ x y x~y i) =
    eqA x~y (go x) (go y) (λ ε δ → go∼ (x~y (ε +₊ δ))) (λ ε → go∼ (x~y ε)) i

  go∼ (ι-ι x y ε x≈y)               = ι-ι-B x y ε x≈y
  go∼ (ι-lim x y ε δ yc Δ r)        = ι-lim-B x y ε δ yc Δ r
                                      (go ∘ y) (λ ε' → go∼ ∘ (yc ε')) (go∼ r)
  go∼ (lim-ι x y ε δ xc Δ r)        = lim-ι-B x y ε δ xc Δ r
                                      (go ∘ x) (λ ε' → go∼ ∘ (xc ε')) (go∼ r)
  go∼ (lim-lim x y ε δ η xc yc Δ r) = lim-lim-B x y ε δ η xc yc Δ r
    (go ∘ x) (λ ε' → go∼ ∘ (xc ε')) (go ∘ y) (λ ε' → go∼ ∘ (yc ε')) (go∼ r)
  go∼ (isProp∼ x ε y p q i)         =
    isProp→PathP (λ i → isPropB (go x) (go y) ε (isProp∼ x ε y p q i))
    (go∼ p) (go∼ q) i

  β-go-ι : ∀ q → go (ι q) ≡ ιA q
  β-go-ι _ = refl

  β-go-lim : ∀ x y → go (lim x y) ≡ limA x y _ _
  β-go-lim _ _ = refl

record Elimℭ∼
  {ℓB} (B : ∀ x y ε → x ∼[ ε ] y → Type ℓB) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓB)) where

  no-eta-equality

  field
    ι-ι-B     : ∀ x y ε x≈y → B (ι x) (ι y) ε (ι-ι x y ε x≈y)
    ι-lim-B   : ∀ x y ε δ yc Δ r
                → B (ι x) (y δ) (ε -₊ δ , Δ) r
                → B (ι x) (lim y yc) ε (ι-lim x y ε δ yc Δ r)
    lim-ι-B   : ∀ x y ε δ xc Δ u
                → B (x δ) (ι y) (ε -₊ δ , Δ) u
                → B (lim x xc) (ι y) ε (lim-ι x y ε δ xc Δ u)
    lim-lim-B : ∀ x y ε δ η xc yc Δ
                → (r : x δ ∼[ ε -₊ (δ +₊ η) , Δ ] y η)
                → B (x δ) (y η) (ε -₊ (δ +₊ η) , Δ) r
                → B (lim x xc) (lim y yc) ε
                    (lim-lim x y ε δ η xc yc Δ r)
    isPropB   : ∀ x y ε u → isProp (B x y ε u)

  go∼ : ∀ {x x' ε} → (r : x ∼[ ε ] x') → B x x' ε r
  go∼ (ι-ι x y ε x≈y)               = ι-ι-B x y ε x≈y
  go∼ (ι-lim x y ε δ yc Δ r)        = ι-lim-B x y ε δ yc Δ r (go∼ r)
  go∼ (lim-ι x y ε δ xc Δ r)        = lim-ι-B x y ε δ xc Δ r (go∼ r)
  go∼ (lim-lim x y ε δ η xc yc Δ r) = lim-lim-B x y ε δ η xc yc Δ r (go∼ r)
  go∼ (isProp∼ x ε y p q i)         =
    isProp→PathP (λ i → isPropB x y ε (isProp∼ x ε y p q i)) (go∼ p) (go∼ q) i

record Elimℭ-Prop {ℓA} (A : ℭM → Type ℓA) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where

  no-eta-equality

  field
    ιA      : ∀ x → A (ι x)
    limA    : ∀ x xc → (∀ q → A (x q)) → A (lim x xc)
    isPropA : ∀ x → isProp (A x)

  go : ∀ x → A x
  go (ι x)           = ιA x
  go (lim x xc)      = limA x xc (go ∘ x)
  go (eqℭ x y x~y i) = isProp→PathP (λ j → isPropA (eqℭ x y x~y j)) (go x) (go y) i

record Elimℭ-Prop2 {ℓA} (A : ℭM → ℭM → Type ℓA) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where

  no-eta-equality

  field
    ι-ιA     : ∀ x y → A (ι x) (ι y)
    ι-limA   : ∀ x y yc → (∀ ε → A (ι x) (y ε)) → A (ι x) (lim y yc)
    lim-ιA   : ∀ x xc y → (∀ ε → A (x ε) (ι y)) → A (lim x xc) (ι y)
    lim-limA : ∀ x xc y yc → (∀ ε δ → A (x ε) (y δ)) → A (lim x xc) (lim y yc)
    isPropA  : ∀ x y → isProp (A x y)

  go : ∀ x y → A x y
  go = Elimℭ-Prop.go e
    where
    e : Elimℭ-Prop (λ x → ∀ y → A x y)
    Elimℭ-Prop.ιA      e x        = Elimℭ-Prop.go e'
      where
      e' : Elimℭ-Prop (A (ι x))
      Elimℭ-Prop.ιA      e' = ι-ιA x
      Elimℭ-Prop.limA    e' = ι-limA x
      Elimℭ-Prop.isPropA e' = isPropA (ι x)
    Elimℭ-Prop.limA    e x xc a∘x = Elimℭ-Prop.go e'
      where
      e' : Elimℭ-Prop (A (lim x xc))
      Elimℭ-Prop.ιA      e' y        = lim-ιA x xc y (flip a∘x (ι y))
      Elimℭ-Prop.limA    e' y yc a∘y = lim-limA x xc y yc (λ ε → a∘x ε ∘ y)
      Elimℭ-Prop.isPropA e'          = isPropA (lim x xc)
    Elimℭ-Prop.isPropA e x       = isPropΠ (isPropA x)

record Elimℭ-Prop2Sym {ℓA} (A : ℭM → ℭM → Type ℓA) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where

  no-eta-equality

  field
    ι-ιA     : ∀ x y → A (ι x) (ι y)
    ι-limA   : ∀ x y yc → (∀ ε → A (ι x) (y ε)) → A (ι x) (lim y yc)
    lim-limA : ∀ x xc y yc → (∀ ε δ → A (x ε) (y δ)) → A (lim x xc) (lim y yc)
    isSymA   : ∀ x y → A x y → A y x
    isPropA  : ∀ x y → isProp (A x y)

  go : ∀ x y → A x y
  go = Elimℭ-Prop2.go e
    where
    e : Elimℭ-Prop2 A
    Elimℭ-Prop2.ι-ιA     e = ι-ιA
    Elimℭ-Prop2.ι-limA   e = ι-limA
    Elimℭ-Prop2.lim-ιA   e =
      λ x xc y r → isSymA (ι y) (lim x xc) (ι-limA y x xc (isSymA _ (ι y) ∘ r))
    Elimℭ-Prop2.lim-limA e = lim-limA
    Elimℭ-Prop2.isPropA  e = isPropA

record Recℭ {ℓA} {ℓB} (A : Type ℓA)
              (B : A → A → ℚ₊ → Type ℓB) : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA        : M → A
    limA      : (a∘x : ℚ₊ → A) → (∀ ε δ → B (a∘x ε) (a∘x δ) (ε +₊ δ)) → A
    eqA       : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

    ι-ι-B     : ∀ x y ε
                → x ≈[ ε ] y
                → B (ιA x) (ιA y) ε
    ι-lim-B   : ∀ x y ε δ yc Δ
                → B (ιA x) (y δ) (ε -₊ δ , Δ)
                → B (ιA x) (limA y yc) ε
    lim-ι-B   : ∀ x y ε δ xc Δ
                → B (x δ) (ιA y) (ε -₊ δ , Δ)
                → B (limA x xc) (ιA y) ε
    lim-lim-B : ∀ x y ε δ η xc yc Δ
                → B (x δ) (y η) (ε -₊ (δ +₊ η) , Δ)
                → B (limA x xc) (limA y yc) ε

    isPropB : ∀ a a' ε → isProp (B a a' ε)

  private
    e : Elimℭ (λ _ → A) λ a a' ε _ → B a a' ε
    Elimℭ.ιA        e          = ιA
    Elimℭ.limA      e _ _ a∘x  = limA a∘x
    Elimℭ.eqA       e _ a a' _ = eqA a a'
    Elimℭ.ι-ι-B     e                                   = ι-ι-B
    Elimℭ.ι-lim-B   e x _ ε δ _ Δ _ a∘y ydc             = ι-lim-B x a∘y ε δ ydc Δ
    Elimℭ.lim-ι-B   e _ y ε δ _ Δ _ a∘x xdc             = lim-ι-B a∘x y ε δ xdc Δ
    Elimℭ.lim-lim-B e _ _ ε δ η _ _ Δ _ a∘x xdc a∘y ydc =
      lim-lim-B a∘x a∘y ε δ η xdc ydc Δ
    Elimℭ.isPropB   e x y ε _ = isPropB x y ε

  go  : ℭM → A
  go∼ : {x y : ℭM} {ε : ℚ₊} (r : x ∼[ ε ] y) → B (go x) (go y) ε

  go  = Elimℭ.go e
  go∼ = Elimℭ.go∼ e

record RecℭSym {ℓA} {ℓB} (A : Type ℓA)
              (B : A → A → ℚ₊ → Type ℓB) : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA        : M → A
    limA      : (a∘x : ℚ₊ → A) → (∀ ε δ → B (a∘x ε) (a∘x δ) (ε +₊ δ)) → A
    eqA       : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

    ι-ι-B     : ∀ x y ε
                → x ≈[ ε ] y
                → B (ιA x) (ιA y) ε
    ι-lim-B   : ∀ x y ε δ yc Δ
                → B (ιA x) (y δ) (ε -₊ δ , Δ)
                → B (ιA x) (limA y yc) ε
    lim-lim-B : ∀ x y ε δ η xc yc Δ
                → B (x δ) (y η) (ε -₊ (δ +₊ η) , Δ)
                → B (limA x xc) (limA y yc) ε

    isSymB  : ∀ a a' ε → B a a' ε → B a' a ε
    isPropB : ∀ a a' ε → isProp (B a a' ε)

  private
    r : Recℭ A B
    Recℭ.ιA        r = ιA
    Recℭ.limA      r = limA
    Recℭ.eqA       r = eqA
    Recℭ.ι-ι-B     r = ι-ι-B
    Recℭ.ι-lim-B   r = ι-lim-B
    Recℭ.lim-ι-B   r = λ x y ε δ xc Δ Bxδ,y →
      isSymB (ιA y) (limA x xc) ε
        (ι-lim-B y x ε δ xc Δ
          (isSymB (x δ) (ιA y) ((ε -₊ δ) , Δ) Bxδ,y))
    Recℭ.lim-lim-B r = lim-lim-B
    Recℭ.isPropB   r = isPropB

  go  : ℭM → A
  go∼ : {x y : ℭM} {ε : ℚ₊} (r : x ∼[ ε ] y) → B (go x) (go y) ε

  go  = Recℭ.go r
  go∼ = Recℭ.go∼ r

record Recℭ∼ {ℓB} (B : ℭM → ℭM → ℚ₊ → Type ℓB) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓB)) where

  no-eta-equality

  field
    ι-ι-B     : ∀ x y ε → (x ≈[ ε ] y) → B (ι x) (ι y) ε
    ι-lim-B   : ∀ x y ε δ yc Δ → (ι x ∼[ ε -₊ δ , Δ ] y δ)
                → B (ι x) (y δ) (ε -₊ δ , Δ)
                → B (ι x) (lim y yc) ε
    lim-ι-B   : ∀ x y ε δ xc Δ → (x δ ∼[ ε -₊ δ , Δ ] ι y)
                → B (x δ) (ι y) (ε -₊ δ , Δ)
                → B (lim x xc) (ι y) ε
    lim-lim-B : ∀ x y ε δ η xc yc Δ
                → (x δ ∼[ ε -₊ (δ +₊ η) , Δ ] y η)
                → B (x δ) (y η) (ε -₊ (δ +₊ η) , Δ)
                → B (lim x xc) (lim y yc) ε
    isPropB   : ∀ x y ε → isProp (B x y ε)

  go∼ : ∀ {x x' ε} → x ∼[ ε ] x' → B x x' ε
  go∼ = Elimℭ∼.go∼ e
    where
    e : Elimℭ∼ λ x x' ε _ → B x x' ε
    Elimℭ∼.ι-ι-B     e = ι-ι-B
    Elimℭ∼.ι-lim-B   e = ι-lim-B
    Elimℭ∼.lim-ι-B   e = lim-ι-B
    Elimℭ∼.lim-lim-B e = lim-lim-B
    Elimℭ∼.isPropB   e = λ x y ε _ → isPropB x y ε

record Casesℭ {ℓA} {ℓB} (A : Type ℓA)
              (B : A → A → ℚ₊ → Type ℓB) : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA        : M → A
    limA      : (x : ℚ₊ → ℭM) → ((δ ε : ℚ₊) → x δ ∼[ δ +₊ ε ] x ε) → A
    eqA       : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

    ι-ι-B     : ∀ x y ε
                → x ≈[ ε ] y
                → B (ιA x) (ιA y) ε
    ι-lim-B   : ∀ x y ε δ yc Δ
                → ι x ∼[ ε -₊ δ , Δ ] y δ
                → (a∘x : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B (a∘x ε') (a∘x δ') (ε' +₊ δ'))
                → B (ιA x) (a∘x δ) (ε -₊ δ , Δ)
                → B (ιA x) (limA y yc) ε
    lim-ι-B   : ∀ x y ε δ xc Δ
                → x δ ∼[ ε -₊ δ , Δ ] ι y
                → (a∘y : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B (a∘y ε') (a∘y δ') (ε' +₊ δ'))
                → B (a∘y δ) (ιA y) (ε -₊ δ , Δ)
                → B (limA x xc) (ιA y) ε
    lim-lim-B : ∀ x y ε δ η xc yc Δ
                → x δ ∼[ ε -₊ (δ +₊ η) , Δ ] y η
                → (a∘x : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B (a∘x ε') (a∘x δ') (ε' +₊ δ'))
                → (a∘y : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B (a∘y ε') (a∘y δ') (ε' +₊ δ'))
                → B (a∘x δ) (a∘y η) (ε -₊ (δ +₊ η) , Δ)
                → B (limA x xc) (limA y yc) ε
    isPropB   : ∀ a a' ε → isProp (B a a' ε)

  private
    e : Elimℭ (λ _ → A) λ a a' ε _ → B a a' ε
    Elimℭ.ιA        e = ιA
    Elimℭ.limA      e = λ x xc _ _ → limA x xc
    Elimℭ.eqA       e = λ _ a a' _ p → eqA a a' p
    Elimℭ.ι-ι-B     e = ι-ι-B
    Elimℭ.ι-lim-B   e = ι-lim-B
    Elimℭ.lim-ι-B   e = lim-ι-B
    Elimℭ.lim-lim-B e = lim-lim-B
    Elimℭ.isPropB   e = λ x y ε _ → isPropB x y ε

  go : ℭM → A
  go = Elimℭ.go e

  go∼ : {x y : ℭM} {ε : ℚ₊} → x ∼[ ε ] y → B (go x) (go y) ε
  go∼ = Elimℭ.go∼ e
