module Cubical.Tactics.CommRingSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec as Vec 
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
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Data.FinData

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
   (0r to 0r‵;1r to 1r‵;_+_ to _+‵_; _·_ to _·‵_; -_ to -‵_ ; _-_ to _-‵_)

 open Exponentiation R' using (_^'_)

 -- module EvalPoly where
 --  open Sum (CommRing→Ring R')

 _^''_ : ⟨R'⟩ → ℕ → Maybe ⟨R'⟩
 x ^'' ℕ.zero = nothing
 x ^'' ℕ.suc n = just (x ^' (ℕ.suc n) )



 _mb·‵mb_ : Maybe ⟨R'⟩ → Maybe ⟨R'⟩ → Maybe ⟨R'⟩
 nothing mb·‵mb x₁ = x₁
 just x mb·‵mb y = just (Mb.rec x (x ·‵_) y)

 mb·‵mbIdR : ∀ x → x mb·‵mb nothing ≡ x 
 mb·‵mbIdR nothing = refl
 mb·‵mbIdR (just x) = refl
 
 Monomial : ℕ → Type
 Monomial n = Vec ℕ n

 evMonomial : ∀ {n} → Monomial n → Vec ⟨R'⟩ n → Maybe ⟨R'⟩
 evMonomial {n = 0} _ _ = nothing
 evMonomial {n = 1} (m ∷ _) (v ∷ _) = v ^'' m 
 evMonomial {n = ℕ.suc (ℕ.suc _)} (m ∷ xs) (v ∷ vs) = (evMonomial xs vs) mb·‵mb (v ^'' m)

 evMonomial∷ : ∀ {n} m ms v vs → evMonomial {ℕ.suc n} (m ∷ ms) (v ∷ vs) ≡
                                   ((evMonomial ms vs) mb·‵mb (v ^'' m)) 
 evMonomial∷ m [] v [] = refl
 evMonomial∷ m (x ∷ ms) v (x₁ ∷ vs) = refl

 PolynomialTerm : ℕ → Type ℓ'
 PolynomialTerm n = Bool × (Maybe ⟨R'⟩) × Monomial n


 -‵[_] : Bool → ⟨R'⟩ → ⟨R'⟩
 -‵[ false ] = -‵_
 -‵[ true ] = idfun _

 _mb·‵_ : Maybe ⟨R'⟩ → ⟨R'⟩ → ⟨R'⟩
 nothing mb·‵ y = y
 just x mb·‵ y = x ·‵ y


 evPolynomialTerm : ∀ {n} → PolynomialTerm n → Vec ⟨R'⟩ n → ⟨R'⟩
 evPolynomialTerm (b , mbK , m) xs = -‵[ b ] (Mb.rec 1r‵ (idfun _) (mbK mb·‵mb evMonomial m xs))

 evPolynomialTerm· : ∀ {n} x v vs →  evPolynomialTerm {n = ℕ.suc n}
      (map-snd (map-snd (λ { (x ∷ xs) → ℕ.suc x ∷ xs })) x) (v ∷ vs)
      ≡ evPolynomialTerm x (v ∷ vs) ·‵ v
 evPolynomialTerm· (b , nothing , x ∷ m) v vs = {!!}
 evPolynomialTerm· (b , just x₁ , x ∷ m) v vs = {!!}
 
 -- Polynomial : ℕ → Type ℓ'
 -- Polynomial n = List (PolynomialTerm n)

 -- evPolynomial :  ∀ {n} → Polynomial n → Vec ⟨R'⟩ n → ⟨R'⟩
 -- evPolynomial [] vs = 0r‵
 -- evPolynomial P[ x ] vs = evPolynomialTerm x vs
 -- evPolynomial (x ∷ xs@(_ ∷ _)) vs = evPolynomial xs vs +‵ evPolynomialTerm x vs

 
 -- Poly·X : ∀ {n} → Polynomial (ℕ.suc n) → Polynomial (ℕ.suc n) 
 -- Poly·X {n} = L.map (map-snd (map-snd λ { (x ∷ xs) → ℕ.suc x ∷ xs  }))

 -- Poly↑ : ∀ {n} → Polynomial n → Polynomial (ℕ.suc n) 
 -- Poly↑ {n} = L.map (map-snd (map-snd (ℕ.zero ∷_)))

 -- evPolynomial∷ : ∀ {n} t p vs → evPolynomial {n = n} (t ∷ p) vs
 --                         ≡ evPolynomial p vs +‵ evPolynomialTerm t vs   
 -- evPolynomial∷ t [] vs = sym (R‵.+IdL _)
 -- evPolynomial∷ t (x ∷ p) vs = refl
 
 -- evPolynomial++ : ∀ {n} p₀ p₁ vs → evPolynomial {n = n} (p₀ L.++ p₁) vs
 --                         ≡ evPolynomial p₁ vs +‵ evPolynomial p₀ vs 
 -- evPolynomial++ [] p₁ vs = sym (R‵.+IdR _)
 -- evPolynomial++ (x ∷ p₀) p₁ vs =
 --      evPolynomial∷ x (p₀ L.++ p₁) vs
 --   ∙∙ cong (_+‵ _) (evPolynomial++ p₀ p₁ vs)
 --      ∙ sym (R‵.+Assoc _ _ _)  
 --   ∙∙ cong (evPolynomial p₁ vs +‵_) (sym (evPolynomial∷ x p₀ vs)  )

 -- evPolynomial·X : ∀ {n} p v vs →
 --      evPolynomial (Poly·X {n} p) (v ∷ vs) ≡
 --      evPolynomial p (v ∷ vs) ·‵ v
 -- evPolynomial·X [] v vs = sym (RT'.0LeftAnnihilates _)
 -- evPolynomial·X (x ∷ p) v vs =
 --      evPolynomial∷ _ (Poly·X p) (v ∷ vs)
 --    ∙∙ cong₂ _+‵_
 --        (evPolynomial·X p v vs)
 --        {!!}
 --    ∙∙ sym (R‵.·DistL+ _ _ v)
 --      ∙ cong (_·‵ v) (sym (evPolynomial∷ _ p _))

 -- -- evPolynomial↑ : ∀ {n} p v vs →
 -- --                    evPolynomial (Poly↑ p) (v ∷ vs) ≡
 -- --                     evPolynomial {n = n} p (vs)
 -- -- evPolynomial↑ [] v vs = refl
 -- -- evPolynomial↑ (x ∷ p) v vs =
 -- --       evPolynomial∷ _ (Poly↑ p) (v ∷ vs)
 -- --    ∙∙ cong₂ _+‵_ (evPolynomial↑ p v vs)
 -- --        (cong (-‵[ x .fst ] ∘ fromJust-def 1r‵ ∘ x .snd .fst mb·‵mb_)
 -- --          (   evMonomial∷ _ _ v vs
 -- --           ∙ mb·‵mbIdR _))
 -- --    ∙∙ sym (evPolynomial∷ _ p vs)

 -- -- Horner→Poly : ∀ {n} → (h : IteratedHornerForms n)
 -- --                     → Σ (Polynomial n) λ pf → ∀ xs → evPolynomial pf xs ≡ eval h xs 
 -- -- Horner→Poly (HornerForms.const x) = [ true , (just (fst hom x)) , [] ] , λ {[] → refl}
 -- -- Horner→Poly HornerForms.0H = [] , λ _ → refl
 -- -- Horner→Poly (h₀ HornerForms.·X+ h₁) =
 -- --  let p₀ , q₀ = Horner→Poly h₀
 -- --      p₁ , q₁ = Horner→Poly h₁
 -- --  in Poly·X p₀ L.++ Poly↑ p₁ , λ { vvs@(v ∷ vs) →
 -- --          evPolynomial++ (Poly·X p₀) (Poly↑ p₁) vvs
 -- --       ∙ R‵.+Comm _ _ ∙ cong₂ _+‵_
 -- --          (evPolynomial·X p₀ v vs ∙ cong (_·‵ v) (q₀ (v ∷ vs)))
 -- --          (evPolynomial↑ p₁ v vs ∙ q₁ vs)}


 -- -- RExpr : (n : ℕ) → Type _
 -- -- RExpr = Expr RRng (fst R')

 -- -- normalize : {n : ℕ} → RExpr n → IteratedHornerForms n
 -- -- normalize {n = n} (K r) = Constant n r
 -- -- normalize {n = n} (∣ k) = Variable n k
 -- -- normalize (x +' y) =
 -- --   (normalize x) +ₕ (normalize y)
 -- -- normalize (x ·' y) =
 -- --   (normalize x) ·ₕ (normalize y)
 -- -- normalize (-' x) =  -ₕ (normalize x)

 -- -- evalConstant : ∀ n r xs → eval (Constant n r) xs ≡ hom .fst r
 -- -- evalConstant ℕ.zero r [] = refl
 -- -- evalConstant (ℕ.suc n) r (x ∷ xs) =
 -- --   RT'.+IdL' _ _ (RT'.0LeftAnnihilates _)
 -- --      ∙ evalConstant n r xs 
 
 -- -- isEqualToNormalform :
 -- --      {n : ℕ} (e : RExpr n) (xs : Vec (fst R') n)
 -- --    → eval (normalize e) xs ≡ ⟦ e ⟧ xs


 -- -- isEqualToNormalform {n = n} (K r) xs = evalConstant n r xs

 -- -- isEqualToNormalform (∣ zero) (x ∷ xs) = 
 -- --   eval 1ₕ (x ∷ xs) ·‵ x +‵ eval 0ₕ xs   ≡⟨ cong (λ u → u ·‵ x +‵ eval 0ₕ xs)
 -- --                                             (Eval1ₕ (x ∷ xs)) ⟩
 -- --   1r‵ ·‵ x +‵ eval 0ₕ xs                 ≡⟨ cong (λ u → 1r‵  ·‵ x +‵ u ) (Eval0H xs) ⟩
 -- --   1r‵ ·‵ x +‵ 0r‵                        ≡⟨ R‵.+IdR _ ⟩
 -- --   1r‵ ·‵ x                             ≡⟨ R‵.·IdL _ ⟩
 -- --   x ∎
 -- -- isEqualToNormalform {n = ℕ.suc n} (∣ (suc k)) (x ∷ xs) =
 -- --     eval 0ₕ (x ∷ xs) ·‵ x +‵ eval (Variable n k) xs ≡⟨ cong (λ u → u ·‵ x +‵ eval (Variable n k) xs)
 -- --                                                             (Eval0H (x ∷ xs)) ⟩
 -- --     0r‵ ·‵ x +‵ eval (Variable n k) xs              ≡⟨ cong (λ u → u +‵ eval (Variable n k) xs)
 -- --                                                             (R‵.0LeftAnnihilates _) ⟩
 -- --     0r‵ +‵ eval (Variable n k) xs                  ≡⟨ R‵.+IdL _ ⟩
 -- --     eval (Variable n k) xs                       ≡⟨ isEqualToNormalform (∣ k) xs ⟩
 -- --     ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

 -- -- isEqualToNormalform (-' e) [] =
 -- --   eval (-ₕ (normalize e)) []  ≡⟨ -EvalDist (normalize e) [] ⟩
 -- --   -‵ eval (normalize e) []    ≡⟨ cong -‵_ (isEqualToNormalform e [] ) ⟩
 -- --   -‵ ⟦ e ⟧ [] ∎
 -- -- isEqualToNormalform (-' e) (x ∷ xs) =
 -- --   eval (-ₕ (normalize e)) (x ∷ xs) ≡⟨ -EvalDist (normalize e) (x ∷ xs) ⟩
 -- --   -‵ eval (normalize e) (x ∷ xs)    ≡⟨ cong -‵_ (isEqualToNormalform e (x ∷ xs) ) ⟩
 -- --   -‵ ⟦ e ⟧ (x ∷ xs) ∎

 -- -- isEqualToNormalform (e +' e₁) [] =
 -- --       eval (normalize e +ₕ normalize e₁) []
 -- --     ≡⟨ +Homeval (normalize e) _ [] ⟩
 -- --       eval (normalize e) []
 -- --       +‵ eval (normalize e₁) []
 -- --     ≡⟨ cong (λ u → u +‵ eval (normalize e₁) [])
 -- --             (isEqualToNormalform e []) ⟩
 -- --       ⟦ e ⟧ []
 -- --       +‵ eval (normalize e₁) []
 -- --     ≡⟨ cong (λ u → ⟦ e ⟧ [] +‵ u) (isEqualToNormalform e₁ []) ⟩
 -- --       ⟦ e ⟧ [] +‵ ⟦ e₁ ⟧ [] ∎
 -- -- isEqualToNormalform (e +' e₁) (x ∷ xs) =
 -- --       eval (normalize e +ₕ normalize e₁) (x ∷ xs)
 -- --     ≡⟨ +Homeval (normalize e) _ (x ∷ xs) ⟩
 -- --       eval (normalize e) (x ∷ xs) +‵ eval (normalize e₁) (x ∷ xs)
 -- --     ≡⟨ cong (λ u → u +‵ eval (normalize e₁) (x ∷ xs))
 -- --             (isEqualToNormalform e (x ∷ xs)) ⟩
 -- --       ⟦ e ⟧ (x ∷ xs) +‵ eval (normalize e₁) (x ∷ xs)
 -- --     ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) +‵ u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
 -- --       ⟦ e ⟧ (x ∷ xs) +‵ ⟦ e₁ ⟧ (x ∷ xs) ∎

 -- -- isEqualToNormalform (e ·' e₁) [] =
 -- --       eval (normalize e ·ₕ normalize e₁) []
 -- --     ≡⟨ ·Homeval (normalize e) _ [] ⟩
 -- --       eval (normalize e) [] ·‵ eval (normalize e₁) []
 -- --     ≡⟨ cong (λ u → u ·‵ eval (normalize e₁) [])
 -- --             (isEqualToNormalform e []) ⟩
 -- --       ⟦ e ⟧ [] ·‵ eval (normalize e₁) []
 -- --     ≡⟨ cong (λ u → ⟦ e ⟧ [] ·‵ u) (isEqualToNormalform e₁ []) ⟩
 -- --       ⟦ e ⟧ [] ·‵ ⟦ e₁ ⟧ [] ∎

 -- -- isEqualToNormalform (e ·' e₁) (x ∷ xs) =
 -- --       eval (normalize e ·ₕ normalize e₁) (x ∷ xs)
 -- --     ≡⟨ ·Homeval (normalize e) _ (x ∷ xs) ⟩
 -- --       eval (normalize e) (x ∷ xs) ·‵ eval (normalize e₁) (x ∷ xs)
 -- --     ≡⟨ cong (λ u → u ·‵ eval (normalize e₁) (x ∷ xs))
 -- --             (isEqualToNormalform e (x ∷ xs)) ⟩
 -- --       ⟦ e ⟧ (x ∷ xs) ·‵ eval (normalize e₁) (x ∷ xs)
 -- --     ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) ·‵ u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
 -- --       ⟦ e ⟧ (x ∷ xs) ·‵ ⟦ e₁ ⟧ (x ∷ xs) ∎


 -- -- [_]ᵗʸ : List (Type ℓ) → Type (ℓ-suc ℓ)
 -- -- [_]ᵗʸ = ListP (idfun _)

  
 -- -- [X]? : ∀ {ℓ'} → Type ℓ'  → Type (ℓ-max (ℓ-suc ℓ) ℓ')
 -- -- [X]? A = (Σ (List (Type ℓ)) (λ XS → (([ XS ]ᵗʸ → A) × (ListP (λ X → Discrete ⟨R⟩ → Maybe X) XS))))

 -- -- ×-[X]? : ∀ {ℓ'} → {A A' : Type ℓ'} → [X]? A → [X]? A' → [X]? (A × A')
 -- -- ×-[X]? (XS , f , d) (XS' , f' , d') =
 -- --   XS L.++ XS' , (map-× f f') ∘S splitP {xs = XS} {XS'} , (d ++P d')
 
 -- -- map-[X]? : ∀ {ℓ'} → {A A' : Type ℓ'} → (A → A')
 -- --           → [X]? A → [X]? A' 
 -- -- map-[X]? f = map-snd (map-fst (f ∘S_))
 

 -- -- IHR?0 : ∀ {n} → ∀ (e : IteratedHornerForms n) →
 -- --           [X]?  (e ≑ 0ₕ) 
 -- -- IHR?0 (HornerForms.const x) = 
 -- --    (([ x ≡ 0r ]) , (λ { (p ∷ []) [] → cong (hom .fst) p} ) ,
 -- --      ((λ _≟_ → decRec just (λ _ → nothing) (x ≟ 0r)) ∷ []))
 -- -- IHR?0 HornerForms.0H = [] , (λ _ xs → Eval0H xs) , [] 
 -- -- IHR?0 (e HornerForms.·X+ e₁) =
 -- --   map-[X]?
 -- --     (λ (f , f') → λ {(v ∷ vs) →
 -- --      cong₂ R‵._+_
 -- --           (RT'.0LeftAnnihilates'  _ _  (f (v ∷ vs)))
 -- --           (f' vs) ∙ RT'.+IdR' _ _ (Eval0H vs) })
 -- --     (×-[X]? (IHR?0 e) (IHR?0 e₁))

   
 -- -- IHR? : ∀ {n} → ∀ (e₁ e₂ : IteratedHornerForms n) →
 -- --     [X]? (e₁ ≑ e₂)
 -- -- IHR? (const x) (const x') = [ x ≡ x' ] , (( λ { (p ∷ []) [] → cong (hom .fst) p }) ,
 -- --   (λ _≟_ → decToMaybe (x ≟ x')) ∷ [])
 -- -- IHR? HornerForms.0H e = map-[X]?
 -- --  (λ f → λ { (v ∷ vs) → sym   (f (v ∷ vs)) }) (IHR?0 e)
 -- -- IHR? e HornerForms.0H =
 -- --    map-[X]?
 -- --  (λ f → λ { (v ∷ vs) → (f (v ∷ vs)) }) (IHR?0 e)
 -- -- IHR? (e HornerForms.·X+ e₁) (e' HornerForms.·X+ e₁') =
 -- --  map-[X]?
 -- --    ((λ (f , f') → λ {(v ∷ vs) →
 -- --       cong₂ R‵._+_ (cong (_·‵ v)  (f (v ∷ vs))) (f' vs)}))
 -- --    (×-[X]? (IHR? e e') (IHR? e₁ e₁'))  


 

  
 -- -- IHR?-refl : ∀ {n} → ∀ (e : IteratedHornerForms n) → [ fst (IHR? e e) ]ᵗʸ
 -- -- IHR?-refl (HornerForms.const x) = refl ∷ []
 -- -- IHR?-refl HornerForms.0H = []
 -- -- IHR?-refl (e HornerForms.·X+ e₁) = IHR?-refl e ++P IHR?-refl e₁



 -- -- solve :
 -- --   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
 -- --   → [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 -- -- solve e₁ e₂ xs z =
 -- --   ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
 -- --   eval (normalize e₁) xs ≡⟨
 -- --     (fst (snd (IHR? (normalize e₁) (normalize e₂))) z xs) ⟩
 -- --   eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
 -- --   ⟦ e₂ ⟧ xs ∎

 -- -- solveByDec :
 -- --   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n) 
 -- --   → [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ
 -- --        ⁇→ (⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs)
 -- -- solveByDec e₁ e₂ xs = ⁇λ solve e₁ e₂ xs 


 -- -- module Decidable (_≟_ : Discrete ⟨R⟩) where

 -- --  HF-Maybe-prfₕ : {n : ℕ} (e₁ e₂ : IteratedHornerForms n) 
 -- --                   → Maybe [ fst (IHR? e₁ e₂) ]ᵗʸ
 -- --  HF-Maybe-prfₕ e₁ e₂ =
 -- --   sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR? e₁ e₂))))


 -- --  HF-Maybe-prf : {n : ℕ} (e₁ e₂ : RExpr n) 
 -- --                   → Maybe [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ
 -- --  HF-Maybe-prf e₁ e₂ = HF-Maybe-prfₕ (normalize e₁) (normalize e₂)



 -- --  normalizeIHF' : ∀ {n} → (e : IteratedHornerForms n) → ((e ≑ 0ₕ) ⊎ Σ _ (e ≑_ ))
  

 -- --  normalizeIHF'  (const x) =
 -- --     decRec (λ x≡0 → inl λ xs i → eval (HornerForms.const (x≡0 i)) xs)
 -- --      (λ _ → inr (HornerForms.const x , λ _ → refl)) (x ≟ 0r)
 -- --  normalizeIHF' 0H = inl λ _ → refl
 -- --  normalizeIHF' e@(e₀ ·X+ e₁) = h (normalizeIHF' e₀) (normalizeIHF' e₁)
 -- --    where
 -- --    h : ((e₀ ≑ 0ₕ) ⊎ Σ _ (e₀ ≑_ )) → ((e₁ ≑ 0ₕ) ⊎ Σ _ (e₁ ≑_ )) → ((e ≑ 0ₕ) ⊎ Σ _ (e ≑_ ))
 -- --    h (inl x₀) (inl x₁) = inl λ { (v ∷ vs) →
 -- --       cong₂ R‵._+_
 -- --           (RT'.0LeftAnnihilates'  _ _  (x₀ (v ∷ vs)))
 -- --           (x₁ vs) ∙ RT'.+IdR' _ _ (Eval0H vs) }
 -- --    h x₀ x₁ =
 -- --      let (u₀ , y₀) = ⊎.rec (0ₕ ,_) (idfun _) x₀
 -- --          (u₁ , y₁) = ⊎.rec (0ₕ ,_) (idfun _) x₁
 -- --      in inr (u₀ ·X+ u₁ , λ { (v ∷ vs) i → y₀ (v ∷ vs) i ·‵ v +‵ y₁ vs i })
    

 -- --  normalizeIHF : ∀ {n} → (e : IteratedHornerForms n) → (Σ _ (e ≑_ ))
 -- --  normalizeIHF = ⊎.rec (0ₕ ,_) (idfun _) ∘ normalizeIHF'

  
 -- --  eval' : {n : ℕ} (P : IteratedHornerForms n)
 -- --         → (xs : Vec ⟨R'⟩ n) → Σ ⟨R'⟩ (_≡ eval P xs )
 -- --  eval' (HornerForms.const x) xs = _ , refl
 -- --  eval' HornerForms.0H xs = _ , refl
 -- --  eval' P@(e₀ HornerForms.·X+ e₁) vvs@(v ∷ vs) =
 -- --    h (normalizeIHF' e₀) (normalizeIHF' e₁)
 -- --   where


 -- --    ₕ·‵ : Σ ⟨R'⟩ (_≡ fst (eval' e₀ vvs) ·‵ v )
 -- --    ₕ·‵ with HF-Maybe-prfₕ e₀ (1ₕ) | HF-Maybe-prfₕ e₀ (-ₕ 1ₕ) 
 -- --    ... | nothing | nothing = _ , refl
 -- --    ... | just x | _ = v , sym (RT'.·IdL' _ _
 -- --       ((snd (eval' e₀ vvs)) ∙∙ (fst (snd (IHR? e₀ (1ₕ))) x vvs) ∙∙
 -- --        Eval1ₕ vvs))
 -- --    ... | _ | just x = -‵ v , sym (RT'.·IdL' _ _
 -- --       (cong -‵_ (((snd (eval' e₀ vvs)) ∙∙ (fst (snd (IHR? e₀ (-ₕ 1ₕ))) x vvs) ∙∙
 -- --          (-EvalDist 1ₕ vvs ∙ cong -‵_ (Eval1ₕ vvs))))
 -- --        ∙ RT'.-Idempotent _))
 -- --     ∙ RT'.-Dist· _ _ 

     


 -- --    h : ((e₀ ≑ 0ₕ) ⊎ Σ _ (e₀ ≑_ )) → ((e₁ ≑ 0ₕ) ⊎ Σ _ (e₁ ≑_ )) → Σ ⟨R'⟩ (_≡ eval P vvs )
 -- --    h (inl x₀) (inl x₁) =  0r‵ , 
 -- --            sym (RT'.0LeftAnnihilates'  _ _  (x₀ vvs))
 -- --        ∙ sym (RT'.+IdR' _ _ (x₁ vs ∙ Eval0H vs))
 -- --    h x₀@(inr _) (inl x₁) =  _ ,
 -- --      snd ₕ·‵ ∙ cong (_·‵ v) (snd (eval' e₀ vvs))
 -- --        ∙ sym (RT'.+IdR' _ _ (x₁ vs ∙ Eval0H vs))
 -- --    h (inl x₁) (inr x) = _ , snd (eval' e₁ vs) ∙ sym (RT'.+IdL' _ _
 -- --       (RT'.0LeftAnnihilates'  _ _  (x₁ vvs)))
 -- --    h (inr x₁) (inr x) = _ , cong₂ _+‵_
 -- --      (snd ₕ·‵ ∙ cong (_·‵ v) (snd (eval' e₀ vvs)))
 -- --      (snd (eval' e₁ vs))


 -- --  solveByDifference :  {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
 -- --     → fst (eval' (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) xs) ≡ 0r‵ → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 -- --  solveByDifference e₁ e₂ xs ev=0 =
 -- --      RT'.equalByDifference _ _ $ 
 -- --         cong₂ _+‵_ (sym (isEqualToNormalform e₁ xs))
 -- --          (cong -‵_ (sym (isEqualToNormalform e₂ xs)) ∙ sym (-EvalDist (normalize e₂) xs))
 -- --          ∙ sym (+Homeval (normalize e₁) (-ₕ (normalize e₂)) xs) ∙
 -- --            snd (normalizeIHF (normalize (e₁ +' -' e₂))) xs ∙
 -- --             sym (snd (eval' (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) xs)) ∙ ev=0
            
 -- -- -- congSolve :
 -- -- --   {n : ℕ} (e₁ e₂ : RExpr n) → ∀ {xs xs' : Vec (fst R') n} → xs ≡ xs'
 -- -- --   → fst (IHR? (normalize e₁) (normalize e₂)) → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs'
 -- -- -- congSolve e₁ e₂ {xs} {xs'} p z =
 -- -- --   ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
 -- -- --   eval (normalize e₁) xs ≡⟨
 -- -- --    cong₂ eval (fst (snd (IHR? (normalize e₁) (normalize e₂))) z) p ⟩
 -- -- --   eval (normalize e₂) xs' ≡⟨ isEqualToNormalform e₂ xs' ⟩
 -- -- --   ⟦ e₂ ⟧ xs' ∎

 -- -- -- solveByPath :
 -- -- --   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
 -- -- --   → eval (normalize e₁) xs ≡ eval (normalize e₂) xs → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 -- -- -- solveByPath e₁ e₂ xs p =
 -- -- --    ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
 -- -- --    eval (normalize e₁) xs ≡⟨ p ⟩
 -- -- --    eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
 -- -- --    ⟦ e₂ ⟧ xs ∎
