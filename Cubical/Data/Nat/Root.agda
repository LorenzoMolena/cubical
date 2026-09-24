module Cubical.Data.Nat.Root where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Nat.BinarySearch

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Binary.Order.Poset.Instances.Nat
open import Cubical.Relation.Binary.Order.Quoset.Instances.Nat
open import Cubical.Relation.Binary.Order.QuosetReasoning
open import Cubical.Relation.Nullary

open <-≤-Reasoning ℕ
  (snd ℕ≤Poset) (snd ℕ<Quoset) (λ _ → <≤-trans) (λ _ → ≤<-trans) <-weaken
open ≤-syntax
open <-syntax
open ≡-syntax

record Rootℕ (b x : ℕ) : Type where
  no-eta-equality
  field
    ⌊_√_⌋  : ℕ
    √^≤   : ⌊_√_⌋ ^ b ≤ x
    <1+√^ : x < (suc ⌊_√_⌋) ^ b

unquoteDecl RootℕIsoΣ = declareRecordIsoΣ RootℕIsoΣ (quote Rootℕ)

private
  lemmaIsPropRootℕ : ∀ b {x r₀ r₁} → x < suc r₀ ^ b → r₁ ^ b ≤ x → ¬ (r₀ < r₁)
  lemmaIsPropRootℕ b {x} {r₀} {r₁} <1+r₀^b r₁^b≤ r₀<r₁ = <-irrefl $
    begin< x <⟨ <1+r₀^b ⟩ suc r₀ ^ b ≤⟨ ≤-^ʳ {k = b} r₀<r₁ ⟩ r₁ ^ b ≤⟨ r₁^b≤ ⟩ x ◾

isPropRootℕ : ∀ b n → isProp (Rootℕ b n)
isPropRootℕ b x = isOfHLevelRetractFromIso 1 RootℕIsoΣ proof where
  proof : isProp (Σ[ r ∈ ℕ ] (r ^ b ≤ x) × (x < suc r ^ b))
  proof (r₀ , r₀^b≤ , <1+r₀^b) (r₁ , r₁^b≤ , <1+r₁^b) with r₀ ≟ r₁
  ... | lt r₀<r₁ = ⊥.rec  (lemmaIsPropRootℕ b <1+r₀^b r₁^b≤ r₀<r₁)
  ... | eq r₀≡r₁ = Σ≡Prop (λ _ → isProp× isProp≤ isProp≤) r₀≡r₁
  ... | gt r₀>r₁ = ⊥.rec  (lemmaIsPropRootℕ b <1+r₁^b r₀^b≤ r₀>r₁)

module RootTheory (rootℕ : ∀ m n → Rootℕ (suc m) n) where
  ⌊_√_⌋ : (b : ℕ) → {1 ≤ᵗ b} → ℕ → ℕ
  ⌊_√_⌋ (suc m) n = Rootℕ.⌊_√_⌋ (rootℕ m n)

  module _ (m : ℕ) where
    private
      b = suc m

      rootℕ^Base : ∀ n → Rootℕ b (n ^ b)
      rootℕ^Base n .Rootℕ.⌊_√_⌋  = n
      rootℕ^Base n .Rootℕ.√^≤   = ≤-refl
      rootℕ^Base n .Rootℕ.<1+√^ = <-^ʳ {k = m} <-suc

      rootℕ0 : Rootℕ b 0
      rootℕ0 .Rootℕ.⌊_√_⌋  = 0
      rootℕ0 .Rootℕ.√^≤   = zero-≤
      rootℕ0 .Rootℕ.<1+√^ = 0<^ b

      rootℕ1 : Rootℕ b 1
      rootℕ1 .Rootℕ.⌊_√_⌋  = 1
      rootℕ1 .Rootℕ.√^≤   = subst (_≤ 1) (sym (1^≡1 b)) ≤-refl
      rootℕ1 .Rootℕ.<1+√^ = 1<^suc m

    isContrRootℕ : ∀ n → isContr (Rootℕ b n)
    isContrRootℕ n .fst = rootℕ m n
    isContrRootℕ n .snd = isPropRootℕ b n (rootℕ m n)

    isUniqueRootℕ : ∀ {n} → (q : Rootℕ b n) → ⌊ b √ n ⌋ ≡ (Rootℕ.⌊_√_⌋ q)
    isUniqueRootℕ = cong Rootℕ.⌊_√_⌋ ∘ snd (isContrRootℕ _)

    root^Base : ∀ n → ⌊ b √ n ^ b ⌋ ≡ n
    root^Base = isUniqueRootℕ ∘ rootℕ^Base

    root0 : ⌊ b √ 0 ⌋ ≡ 0
    root0 = isUniqueRootℕ rootℕ0

    root1 : ⌊ b √ 1 ⌋ ≡ 1
    root1 = isUniqueRootℕ rootℕ1

    √Mono≤ : ∀ x y → x ≤ y → ⌊ b √ x ⌋ ≤ ⌊ b √ y ⌋
    √Mono≤ x y x≤y = <-asym' λ √y<√x → flip <-asym (≤-^ʳ {k = b} √y<√x) $ begin<
      ⌊ b √ x ⌋ ^ b      ≤⟨ Rootℕ.√^≤ (rootℕ m x) ⟩
      x                 ≤⟨ x≤y ⟩
      y                 <⟨ Rootℕ.<1+√^ (rootℕ m y) ⟩
      suc ⌊ b √ y ⌋ ^ b ◾

module RootCore (m n : ℕ) where
  private
    b = suc m
    Σ<ᵇ : Σ[ k ∈ ℕ ] n <ᵗ k ^ b
    Σ<ᵇ = (suc n , <→<ᵗ (L≤^suc (suc n) m))
  open BiggestImage≤.→Biggest (_^ b) (≤-^ʳ {k = b}) refl n Σ<ᵇ public renaming
    (preimage to ⌊1+_√_⌋ ; <imageSuc to <⌊1+_√1+_⌋ ; image≤ to ⌊1+_√_⌋≤)

rootℕ : ∀ m n → Rootℕ (suc m) n
rootℕ m n .Rootℕ.⌊_√_⌋  = RootCore.⌊1+ m √ n ⌋
rootℕ m n .Rootℕ.√^≤   = RootCore.⌊1+ m √ n ⌋≤
rootℕ m n .Rootℕ.<1+√^ = RootCore.<⌊1+ m √1+ n ⌋

open RootTheory (rootℕ) public

⌊√_⌋ ⌊³√_⌋ : ℕ → ℕ
⌊√_⌋  = ⌊ 2 √_⌋
⌊³√_⌋ = ⌊ 3 √_⌋

private
  _ : ⌊√ 64 ⌋ ≡ 8
  _ = refl

  _ : ⌊√ 63 ⌋ ≡ 7
  _ = refl

  _ : ⌊√ 65 ⌋ ≡ 8
  _ = refl

  _ : ⌊³√ 64 ⌋ ≡ 4
  _ = refl

  toDigits : (n : ℕ) → {1 ≤ᵗ n} → ℕ → ℕ → ℕ × ℕ
  toDigits n@(suc n-1) x d =
    let root = ⌊ n √ x · (10 ^ n) ^ d ⌋
    in quotient root / (10 ^ d) , remainder root / (10 ^ d)

  √2Digits  = toDigits 2 2
  ³√2Digits = toDigits 3 2

  _ : √2Digits 20 ≡ (1 , 41421356237309504880)
  _ = refl

  _ : ³√2Digits 20 ≡ (1 , 25992104989487316476)
  _ = refl
