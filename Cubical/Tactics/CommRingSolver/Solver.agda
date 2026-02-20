module Cubical.Tactics.CommRingSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Data.Sigma
import Cubical.Data.Prod as ×
open import Cubical.Data.Empty
open import Cubical.Data.List as L
open import Cubical.Data.List.Dependent
open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Relation.Nullary

open import Cubical.Reflection.Sugar

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Tactics.CommRingSolver.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Tactics.CommRingSolver.AlgebraExpression
open import Cubical.Tactics.CommRingSolver.HornerForms
open import Cubical.Tactics.CommRingSolver.RawRing
open import Cubical.Tactics.CommRingSolver.EvalHom

private
  variable
    ℓ ℓ' : Level

module EqualityToNormalform (R@(⟨R⟩ , _) : CommRing ℓ)
                         -- (_≟_ : Discrete ⟨R⟩ )
                         (R'@(⟨R'⟩ , _) : CommRing ℓ')
                         (hom@(scalar‵ , _) : CommRingHom R R') where

 open CommRingStr (snd R)

 open RingTheory (CommRing→Ring R)


 open HomomorphismProperties R  R' hom
 open IsCommRingHom (snd hom)

 open CommRingStr (snd R') using () renaming
   (0r to 0r‵;1r to 1r‵;_+_ to _+‵_; _·_ to _·‵_; -_ to -‵_)


 RExpr : (n : ℕ) → Type _
 RExpr = Expr RRng (fst R')

 normalize : {n : ℕ} → RExpr n → IteratedHornerForms n
 normalize {n = n} (K r) = Constant n r
 normalize {n = n} (∣ k) = Variable n k
 normalize (x +' y) =
   (normalize x) +ₕ (normalize y)
 normalize (x ·' y) =
   (normalize x) ·ₕ (normalize y)
 normalize (-' x) =  -ₕ (normalize x)

 evalConstant : ∀ n r xs → eval (Constant n r) xs ≡ hom .fst r
 evalConstant ℕ.zero r [] = refl
 evalConstant (ℕ.suc n) r (x ∷ xs) =
   RT'.+IdL' _ _ (RT'.0LeftAnnihilates _)
      ∙ evalConstant n r xs 
 
 isEqualToNormalform :
      {n : ℕ} (e : RExpr n) (xs : Vec (fst R') n)
    → eval (normalize e) xs ≡ ⟦ e ⟧ xs


 isEqualToNormalform {n = n} (K r) xs = evalConstant n r xs

 isEqualToNormalform (∣ zero) (x ∷ xs) = 
   eval 1ₕ (x ∷ xs) ·‵ x +‵ eval 0ₕ xs   ≡⟨ cong (λ u → u ·‵ x +‵ eval 0ₕ xs)
                                             (Eval1ₕ (x ∷ xs)) ⟩
   1r‵ ·‵ x +‵ eval 0ₕ xs                 ≡⟨ cong (λ u → 1r‵  ·‵ x +‵ u ) (Eval0H xs) ⟩
   1r‵ ·‵ x +‵ 0r‵                        ≡⟨ R‵.+IdR _ ⟩
   1r‵ ·‵ x                             ≡⟨ R‵.·IdL _ ⟩
   x ∎
 isEqualToNormalform {n = ℕ.suc n} (∣ (suc k)) (x ∷ xs) =
     eval 0ₕ (x ∷ xs) ·‵ x +‵ eval (Variable n k) xs ≡⟨ cong (λ u → u ·‵ x +‵ eval (Variable n k) xs)
                                                             (Eval0H (x ∷ xs)) ⟩
     0r‵ ·‵ x +‵ eval (Variable n k) xs              ≡⟨ cong (λ u → u +‵ eval (Variable n k) xs)
                                                             (R‵.0LeftAnnihilates _) ⟩
     0r‵ +‵ eval (Variable n k) xs                  ≡⟨ R‵.+IdL _ ⟩
     eval (Variable n k) xs                       ≡⟨ isEqualToNormalform (∣ k) xs ⟩
     ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

 isEqualToNormalform (-' e) [] =
   eval (-ₕ (normalize e)) []  ≡⟨ -EvalDist (normalize e) [] ⟩
   -‵ eval (normalize e) []    ≡⟨ cong -‵_ (isEqualToNormalform e [] ) ⟩
   -‵ ⟦ e ⟧ [] ∎
 isEqualToNormalform (-' e) (x ∷ xs) =
   eval (-ₕ (normalize e)) (x ∷ xs) ≡⟨ -EvalDist (normalize e) (x ∷ xs) ⟩
   -‵ eval (normalize e) (x ∷ xs)    ≡⟨ cong -‵_ (isEqualToNormalform e (x ∷ xs) ) ⟩
   -‵ ⟦ e ⟧ (x ∷ xs) ∎

 isEqualToNormalform (e +' e₁) [] =
       eval (normalize e +ₕ normalize e₁) []
     ≡⟨ +Homeval (normalize e) _ [] ⟩
       eval (normalize e) []
       +‵ eval (normalize e₁) []
     ≡⟨ cong (λ u → u +‵ eval (normalize e₁) [])
             (isEqualToNormalform e []) ⟩
       ⟦ e ⟧ []
       +‵ eval (normalize e₁) []
     ≡⟨ cong (λ u → ⟦ e ⟧ [] +‵ u) (isEqualToNormalform e₁ []) ⟩
       ⟦ e ⟧ [] +‵ ⟦ e₁ ⟧ [] ∎
 isEqualToNormalform (e +' e₁) (x ∷ xs) =
       eval (normalize e +ₕ normalize e₁) (x ∷ xs)
     ≡⟨ +Homeval (normalize e) _ (x ∷ xs) ⟩
       eval (normalize e) (x ∷ xs) +‵ eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → u +‵ eval (normalize e₁) (x ∷ xs))
             (isEqualToNormalform e (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) +‵ eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) +‵ u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) +‵ ⟦ e₁ ⟧ (x ∷ xs) ∎

 isEqualToNormalform (e ·' e₁) [] =
       eval (normalize e ·ₕ normalize e₁) []
     ≡⟨ ·Homeval (normalize e) _ [] ⟩
       eval (normalize e) [] ·‵ eval (normalize e₁) []
     ≡⟨ cong (λ u → u ·‵ eval (normalize e₁) [])
             (isEqualToNormalform e []) ⟩
       ⟦ e ⟧ [] ·‵ eval (normalize e₁) []
     ≡⟨ cong (λ u → ⟦ e ⟧ [] ·‵ u) (isEqualToNormalform e₁ []) ⟩
       ⟦ e ⟧ [] ·‵ ⟦ e₁ ⟧ [] ∎

 isEqualToNormalform (e ·' e₁) (x ∷ xs) =
       eval (normalize e ·ₕ normalize e₁) (x ∷ xs)
     ≡⟨ ·Homeval (normalize e) _ (x ∷ xs) ⟩
       eval (normalize e) (x ∷ xs) ·‵ eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → u ·‵ eval (normalize e₁) (x ∷ xs))
             (isEqualToNormalform e (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) ·‵ eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) ·‵ u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) ·‵ ⟦ e₁ ⟧ (x ∷ xs) ∎


 [_]ᵗʸ : List (Type ℓ) → Type (ℓ-suc ℓ)
 [_]ᵗʸ = ListP (idfun _)

  
 [X]? : ∀ {ℓ'} → Type ℓ'  → Type (ℓ-max (ℓ-suc ℓ) ℓ')
 [X]? A = (Σ (List (Type ℓ)) (λ XS → (([ XS ]ᵗʸ → A) × (ListP (λ X → Discrete ⟨R⟩ → Maybe X) XS))))

 ×-[X]? : ∀ {ℓ'} → {A A' : Type ℓ'} → [X]? A → [X]? A' → [X]? (A × A')
 ×-[X]? (XS , f , d) (XS' , f' , d') =
   XS L.++ XS' , (map-× f f') ∘S splitP {xs = XS} {XS'} , (d ++P d')
 
 map-[X]? : ∀ {ℓ'} → {A A' : Type ℓ'} → (A → A')
           → [X]? A → [X]? A' 
 map-[X]? f = map-snd (map-fst (f ∘S_))
 

 IHR?0 : ∀ {n} → ∀ (e : IteratedHornerForms n) →
           [X]? (∀ xs → eval e xs ≡ R‵.0r)
 IHR?0 (HornerForms.const x) =
    (([ x ≡ 0r ]) , (λ { (p ∷ []) [] → cong (hom .fst) p ∙ Eval0H [] } ) ,
      ((λ _≟_ → decRec just (λ _ → nothing) (x ≟ 0r)) ∷ []))
 IHR?0 HornerForms.0H = [] , (λ _ xs → Eval0H xs) , [] 
 IHR?0 (e HornerForms.·X+ e₁) =
   map-[X]?
     (λ (f , f') → λ {(v ∷ vs) →
      cong₂ R‵._+_
           (RT'.0LeftAnnihilates'  _ _  (f (v ∷ vs)))
           (f' vs) ∙ RT'.0Idempotent})
     (×-[X]? (IHR?0 e) (IHR?0 e₁))

   
 IHR? : ∀ {n} → ∀ (e₁ e₂ : IteratedHornerForms n) →
     [X]? (∀ xs → eval e₁ xs ≡ eval e₂ xs)
 IHR? (const x) (const x') = [ x ≡ x' ] , (( λ { (p ∷ []) [] → cong (hom .fst) p }) ,
   (λ _≟_ → decToMaybe (x ≟ x')) ∷ [])
 IHR? HornerForms.0H e = map-[X]?
  (λ f → λ { (v ∷ vs) → sym   (f (v ∷ vs)) }) (IHR?0 e)
 IHR? e HornerForms.0H =
    map-[X]?
  (λ f → λ { (v ∷ vs) → (f (v ∷ vs)) }) (IHR?0 e)
 IHR? (e HornerForms.·X+ e₁) (e' HornerForms.·X+ e₁') =
  map-[X]?
    ((λ (f , f') → λ {(v ∷ vs) →
       cong₂ R‵._+_ (cong (_·‵ v)  (f (v ∷ vs))) (f' vs)}))
    (×-[X]? (IHR? e e') (IHR? e₁ e₁'))  


 IHR?-refl : ∀ {n} → ∀ (e : IteratedHornerForms n) → [ fst (IHR? e e) ]ᵗʸ
 IHR?-refl (HornerForms.const x) = refl ∷ []
 IHR?-refl HornerForms.0H = []
 IHR?-refl (e HornerForms.·X+ e₁) = IHR?-refl e ++P IHR?-refl e₁



 solve :
   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
   → [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 solve e₁ e₂ xs z =
   ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
   eval (normalize e₁) xs ≡⟨
     (fst (snd (IHR? (normalize e₁) (normalize e₂))) z xs) ⟩
   eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
   ⟦ e₂ ⟧ xs ∎

 solveByDec :
   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n) 
   → [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ
        ⁇→ (⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs)
 solveByDec e₁ e₂ xs = ⁇λ solve e₁ e₂ xs 


 module Decidable (_≟_ : Discrete ⟨R⟩) where
 
  HF-Maybe-prf : {n : ℕ} (e₁ e₂ : RExpr n) 
                   → Maybe [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ
  HF-Maybe-prf e₁ e₂ =
   sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR? (normalize e₁) (normalize e₂)))))


 -- -- congSolve :
 -- --   {n : ℕ} (e₁ e₂ : RExpr n) → ∀ {xs xs' : Vec (fst R') n} → xs ≡ xs'
 -- --   → fst (IHR? (normalize e₁) (normalize e₂)) → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs'
 -- -- congSolve e₁ e₂ {xs} {xs'} p z =
 -- --   ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
 -- --   eval (normalize e₁) xs ≡⟨
 -- --    cong₂ eval (fst (snd (IHR? (normalize e₁) (normalize e₂))) z) p ⟩
 -- --   eval (normalize e₂) xs' ≡⟨ isEqualToNormalform e₂ xs' ⟩
 -- --   ⟦ e₂ ⟧ xs' ∎

 -- -- solveByPath :
 -- --   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
 -- --   → eval (normalize e₁) xs ≡ eval (normalize e₂) xs → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 -- -- solveByPath e₁ e₂ xs p =
 -- --    ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
 -- --    eval (normalize e₁) xs ≡⟨ p ⟩
 -- --    eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
 -- --    ⟦ e₂ ⟧ xs ∎
