module Cubical.Relation.Premetric.Mappings.NotUnivalentL where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as ⊥

open import Cubical.Categories.Category.Base

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals.Fast
open import Cubical.Algebra.Ring.Properties

open import Cubical.Data.Int.Fast as ℤ using ()
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Rationals.Fast.Base as ℚ
import Cubical.Data.Rationals.Fast.Properties as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚOrd using (pos<pos)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals.Fast
open import Cubical.Relation.Nullary

open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing
open CanonicalEmbeddings ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals

private
  module RT = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)

open CategoryStructures using (idⁿ ; L≡)
  renaming (PremetricSpaceCategoryᴸ to PrSpacesᴸ)

private
  module Q = PremetricStr (snd ℚPremetricSpace)

  half : ℚ
  half = [ 1 / 2 ]

  two : ℚ
  two = 1r + 1r

  half₊ : ℚ₊
  half₊ = [ 1 / 2 ]₊

  two₊ : ℚ₊
  two₊ = [ 2 / 1 ]₊

  threeHalf : ℚ₊
  threeHalf = [ 3 / 2 ]₊

  two< : 0r < two
  two< = pos<pos tt

  two≤ : 0r ≤ two
  two≤ = <-≤-weaken _ _ two<

  half<one : half < 1r
  half<one = subst (half <_) 1/2+1/2≡1 (<SumLeftPos half half 0<1/2)

  half≤one : half ≤ 1r
  half≤one = <-≤-weaken _ _ half<one

  one<threeHalf : 1r < ⟨ threeHalf ⟩₊
  one<threeHalf = pos<pos tt

  threeHalf≤two : ⟨ threeHalf ⟩₊ ≤ two
  threeHalf≤two = <-≤-weaken _ _ $ begin<
    ⟨ threeHalf ⟩₊ ≡→≤⟨ +Comm 1r half ⟩
    half + 1r      <⟨ +MonoR< half 1r 1r half<one ⟩
    two            ◾

  scale2 : ℚ → ℚ
  scale2 = two ·_

  scaleHalf : ℚ → ℚ
  scaleHalf = half ·_

  scale2-diff : ∀ x y → scale2 x - scale2 y ≡ two · (x - y)
  scale2-diff x y = sym (RT.·DistR- two x y)

  scaleHalf-diff : ∀ x y → scaleHalf x - scaleHalf y ≡ half · (x - y)
  scaleHalf-diff x y = sym (RT.·DistR- half x y)

  scale2-one-minus-zero : scale2 1r - scale2 0r ≡ two
  scale2-one-minus-zero =
    scale2-diff 1r 0r
    ∙ cong (two ·_) (cong (1r +_) RT.0Selfinverse ∙ +IdR 1r)
    ∙ ·IdR two

  scale2ᴸ : L[ ℚPremetricSpace , ℚPremetricSpace ]
  fst scale2ᴸ = scale2
  snd scale2ᴸ = ∣ (two₊ , islipschitzwith λ x y ε x≈y →
    subst (_< ⟨ two₊ ·₊ ε ⟩₊) (sym (cong abs (scale2-diff x y)))
      (≤-<-trans _ _ _
        (0≤→abs·≤ two (x - y) two≤)
        (·MonoL< (abs (x - y)) ⟨ ε ⟩₊ two two< x≈y))) ∣₁

  halfAbs≤abs : ∀ z → half · abs z ≤ abs z
  halfAbs≤abs z = begin≤
    half · abs z      ≡→≤⟨ ·Comm half (abs z) ⟩
    abs z · half      ≤⟨ ·MonoL≤ half 1r (abs z) (0≤abs z) half≤one ⟩
    abs z · 1r        ≡→≤⟨ ·IdR (abs z) ⟩
    abs z             ◾

  half·two≡1 : half · two ≡ 1r
  half·two≡1 =
    ·DistR+ half 1r 1r ∙ cong₂ _+_ (·IdR half) (·IdR half) ∙ 1/2+1/2≡1

  scaleHalfⁿ : NE[ ℚPremetricSpace , ℚPremetricSpace ]
  fst scaleHalfⁿ = scaleHalf
  IsNonExpanding.pres≈ (snd scaleHalfⁿ) x y ε x≈y =
    subst (_< ⟨ ε ⟩₊) (sym (cong abs (scaleHalf-diff x y)))
      (≤-<-trans _ _ _
        (begin≤
          abs (half · (x - y))  ≤⟨ 0≤→abs·≤ half (x - y) 0≤1/2 ⟩
          half · abs (x - y)    ≤⟨ halfAbs≤abs (x - y) ⟩
          abs (x - y)           ◾)
        x≈y)

  scaleHalfᴸ : L[ ℚPremetricSpace , ℚPremetricSpace ]
  scaleHalfᴸ = NE→L scaleHalfⁿ

  scale2Iso : CatIso (PrSpacesᴸ ℓ-zero ℓ-zero) ℚPremetricSpace ℚPremetricSpace
  scale2Iso = scale2ᴸ , isiso scaleHalfᴸ sec ret
    where
    sec : scaleHalfᴸ ⋆⟨ PrSpacesᴸ ℓ-zero ℓ-zero ⟩ scale2ᴸ ≡ Category.id (PrSpacesᴸ ℓ-zero ℓ-zero)
    sec = L≡ (funExt λ x →
      scale2 (scaleHalf x)  ≡⟨ ·Assoc two half x ⟩
      (two · half) · x      ≡⟨ cong (_· x) (·Comm two half ∙ half·two≡1) ⟩
      1r · x                ≡⟨ OrderedCommRingStr.·IdL (snd ℚOrderedCommRing) x ⟩
      x                     ∎)

    ret : scale2ᴸ ⋆⟨ PrSpacesᴸ ℓ-zero ℓ-zero ⟩ scaleHalfᴸ ≡ Category.id (PrSpacesᴸ ℓ-zero ℓ-zero)
    ret = L≡ (funExt λ x →
      scaleHalf (scale2 x)  ≡⟨ ·Assoc half two x ⟩
      (half · two) · x      ≡⟨ cong (_· x) half·two≡1 ⟩
      1r · x                ≡⟨ OrderedCommRingStr.·IdL (snd ℚOrderedCommRing) x ⟩
      x                     ∎)

  transport→IsNonExpanding
    : ∀ {M N : PremetricSpace ℓ-zero ℓ-zero} (p : M ≡ N)
    → IsNonExpanding (M .snd) (transport (cong fst p)) (N .snd)
  transport→IsNonExpanding {M = M} =
    J (λ N p → IsNonExpanding (M .snd) (transport (cong fst p)) (N .snd))
      (isnonexpanding λ x y ε x≈y →
        subst2
          (λ a b → PremetricStr._≈[_]_ (M .snd) a ε b)
          (sym (transportRefl x))
          (sym (transportRefl y))
          x≈y)

  pathToIsoFun≡transport
    : ∀ {M N : PremetricSpace ℓ-zero ℓ-zero} (p : M ≡ N)
    → fst (fst (pathToIso {C = PrSpacesᴸ ℓ-zero ℓ-zero} p)) ≡ transport (cong fst p)
  pathToIsoFun≡transport {M = M} =
    J
      (λ _ p → fst (fst (pathToIso {C = PrSpacesᴸ ℓ-zero ℓ-zero} p)) ≡ transport (cong fst p))
      (cong (fst ∘ fst) (pathToIso-refl {C = PrSpacesᴸ ℓ-zero ℓ-zero} {x = M})
      ∙ funExt (sym ∘ transportRefl))

  pathToIsoᴸ→IsNonExpanding
    : ∀ {M N : PremetricSpace ℓ-zero ℓ-zero} (p : M ≡ N)
    → IsNonExpanding (M .snd) (fst (fst (pathToIso {C = PrSpacesᴸ ℓ-zero ℓ-zero} p))) (N .snd)
  pathToIsoᴸ→IsNonExpanding {M = M} {N = N} p =
    subst
      (λ f → IsNonExpanding (M .snd) f (N .snd))
      (sym (pathToIsoFun≡transport p))
      (transport→IsNonExpanding p)

  one≈zero : 1r Q.≈[ threeHalf ] 0r
  one≈zero =
    subst (_< ⟨ threeHalf ⟩₊)
      (cong abs (cong (1r +_) RT.0Selfinverse ∙ +IdR 1r) ∙ abs1)
      one<threeHalf

  scale2-one≉zero : ¬ scale2 1r Q.≈[ threeHalf ] scale2 0r
  scale2-one≉zero =
    ≤→¬> ⟨ threeHalf ⟩₊ two threeHalf≤two
    ∘ subst (_< ⟨ threeHalf ⟩₊)
        (cong abs scale2-one-minus-zero
        ∙ 0≤→abs≡id two two≤)

¬isUnivalentPrSpacesᴸ : ¬ isUnivalent (PrSpacesᴸ ℓ-zero ℓ-zero)
¬isUnivalentPrSpacesᴸ isUniv = scale2-one≉zero (IsNonExpanding.pres≈ scale2-isNE 1r 0r threeHalf one≈zero)
  where
  open isUnivalent isUniv

  p : ℚPremetricSpace ≡ ℚPremetricSpace
  p = CatIsoToPath scale2Iso

  pathToIso≡scale2 : pathToIso {C = PrSpacesᴸ ℓ-zero ℓ-zero} p ≡ scale2Iso
  pathToIso≡scale2 = secEq (univEquiv _ _) scale2Iso

  scale2-isNE : IsNonExpanding (snd ℚPremetricSpace) scale2 (snd ℚPremetricSpace)
  scale2-isNE =
    subst
      (λ f → IsNonExpanding (snd ℚPremetricSpace) f (snd ℚPremetricSpace))
      (cong (fst ∘ fst) pathToIso≡scale2)
      (pathToIsoᴸ→IsNonExpanding p)
