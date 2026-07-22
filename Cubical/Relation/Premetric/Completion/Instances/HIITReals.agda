module Cubical.Relation.Premetric.Completion.Instances.HIITReals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Fast.Int as ℤ using (ℤ ; pos ; neg ; negsuc)
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Instances.Rationals as ℚ using (ℚPremetricSpace)
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.Base ℚPremetricSpace public renaming
  (ℭ to ℝ ; ι to rat ; eqℭ to eqℝ ; ι-ι to rat-rat ; ι-lim to rat-lim ; lim-ι to lim-rat)
open import  Cubical.Relation.Premetric.Completion.Lift

open import  Cubical.Relation.Premetric.Completion.Properties _ ℚPremetricSpace public
  renaming (ℭPremetricSpace to ℝPremetricSpace ; isCompleteℭ to isCompleteℝ ;
    ιⁿ to ratⁿ ; ιᶜ to ratᶜ ; ιᵘᶜ to ratᵘᶜ ; ιᴸ to ratᴸ)

open LiftCompleteCodomain ℚPremetricSpace ℝPremetricSpace isCompleteℝ
open LiftCompleteCodomain₂ ℚPremetricSpace ℚPremetricSpace ℝPremetricSpace isCompleteℝ
open ∘Properties ℚPremetricSpace using (_ⁿ∘ⁿ-)
open ∘Properties ℝPremetricSpace using (-∘ⁿ_)

pattern Δrat< p = rat-rat (ℚ.pos<pos p)

-ⁿ : NE[ ℝPremetricSpace , ℝPremetricSpace ]
-ⁿ = liftNE (ratⁿ ∘NE ℚ.-ⁿ)

-_ : ℝ → ℝ
-_ = fst -ⁿ

+ⁿ : NE[ ℝPremetricSpace , NE[ ℝPremetricSpace , ℝPremetricSpace ]PrSpace ]
+ⁿ = liftNE₂ ((ratⁿ ⁿ∘ⁿ-) ∘NE ℚ.+ⁿ)

_+_ : ℝ → ℝ → ℝ
_+_ = fst ∘ (fst +ⁿ)

-₂ⁿ : NE[ ℝPremetricSpace , NE[ ℝPremetricSpace , ℝPremetricSpace ]PrSpace ]
-₂ⁿ = (-∘ⁿ -ⁿ) ∘NE +ⁿ

_-_ : ℝ → ℝ → ℝ
_-_ = fst ∘ (fst -₂ⁿ)

+IdL : ∀ x → (rat 0) + x ≡ x
+IdL = nonExpansive≡ _ _ (fst +ⁿ (rat 0)) idⁿ (cong rat ∘ ℚ.+IdL)

+IdR : ∀ x → x + (rat 0) ≡ x
+IdR = nonExpansive≡ _ _ (fst (flipNE +ⁿ) (rat 0)) idⁿ (cong rat ∘ ℚ.+IdR)

+Comm : ∀ x y → x + y ≡ y + x
+Comm = nonExpansive₂≡ _ _ _ +ⁿ (flipNE +ⁿ) ((cong rat ∘_) ∘ ℚ.+Comm)


-- Natural number and negative integer literals for ℝ

open import Cubical.Data.Nat.Literals public

instance
  fromNatℝ : HasFromNat ℝ
  fromNatℝ = record { Constraint = λ _ → Unit ; fromNat = λ n → rat [ pos n / 1 ] }

instance
  fromNegℝ : HasFromNeg ℝ
  fromNegℝ = record { Constraint = λ _ → Unit ; fromNeg = λ n → rat [ neg n / 1 ] }

private
  _ : -12297292 ∼[ 2178271827 , pos<pos tt ] -12296294
  _ = Δrat< tt

  _ : ∀ {x y} → x - y ≡ x + (- y)
  _ = refl

  _ : ∀ {x xc} → 2 + (lim x xc) ≡ lim (λ ε → 2 + (x ε)) _
  _ = refl
