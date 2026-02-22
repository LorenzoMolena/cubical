module Cubical.Tactics.CommRingSolver.HornerEval where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Vec
open import Cubical.Data.Bool as 𝟚

open import Cubical.Relation.Nullary

open import Cubical.Tactics.CommRingSolver.Utility
open import Cubical.Tactics.CommRingSolver.RawRing
open import Cubical.Tactics.CommRingSolver.RawAlgebra
open import Cubical.Tactics.CommRingSolver.HornerForms
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring


private
  variable
    ℓ ℓ' : Level


module HornerEval (R@(⟨R⟩ , _) : CommRing ℓ)
                         -- (_≟_ : Discrete ⟨R⟩ )
                         (R'@(⟨R'⟩ , _) : CommRing ℓ')
                         (hom@(scalar‵ , _) : CommRingHom R R') where
 open CommRingStr (snd R)

 open RingTheory (CommRing→Ring R)


 open HornerForms R R' hom public
 open IteratedHornerOperations public

 open IsCommRingHom (snd hom)

 open CommRingStr (snd R') using () renaming
   (0r to 0r‵;1r to 1r‵;_+_ to _+‵_; _·_ to _·‵_; -_ to -‵_)



 eval : {n : ℕ} (P : IteratedHornerForms n)
        → Vec ⟨R'⟩ n → ⟨R'⟩
 eval  (const r) [] = scalar‵ r
 eval 0H _ = 0r‵
 eval (P ·X+ Q) (x ∷ xs) =
      let
          P' = (eval P (x ∷ xs))
          Q' = eval Q xs
      in ((P' ·‵ x) +‵ Q')

 

 _≑_ : ∀ {n} → IteratedHornerForms n → IteratedHornerForms n → Type ℓ'
 P ≑ Q = ∀ xs → eval P xs ≡ eval Q xs

