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
open import Cubical.Data.NatPlusOne
open import Cubical.Data.List as L hiding (drop)
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
                          (R'@(⟨R'⟩ , _) : CommRing ℓ')
                         (hom@(scalar‵ , _) : CommRingHom R R') where

 open CommRingStr (snd R)

 open RingTheory (CommRing→Ring R)


 open HomomorphismProperties R  R' hom
 open IsCommRingHom (snd hom)

 open CommRingStr (snd R') using () renaming
   (0r to 0r‵;1r to 1r‵;_+_ to _+‵_; _·_ to _·‵_; -_ to -‵_ ; _-_ to _-‵_)

 open Exponentiation R' using (_^_ ; _^'_ ; ^'≡^)

 -- module EvalPoly where
 --  open Sum (CommRing→Ring R')

 _^''_ : ⟨R'⟩ → ℕ → Maybe ⟨R'⟩
 x ^'' ℕ.zero = nothing
 x ^'' ℕ.suc ℕ.zero = just x
 x ^'' ℕ.suc n = just (x ^' (ℕ.suc n) )

 ^''-suc : ∀ m v → v ^' ℕ.suc m ≡ v ^' m ·‵ v
 ^''-suc ℕ.zero v = sym (R‵.·IdL _)
 ^''-suc one v = refl
 ^''-suc (ℕ.suc (ℕ.suc m)) v = R‵.·Comm _ _

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

 PolynomialTerm : ℕ → Type ℓ
 PolynomialTerm n = Bool × (Maybe ⟨R⟩) × Monomial n


 -‵[_] : Bool → ⟨R'⟩ → ⟨R'⟩
 -‵[ false ] = -‵_
 -‵[ true ] = idfun _

 -‵[_]· : ∀ b x y → (-‵[ b ] x) ·‵ y ≡ -‵[ b ] (x ·‵ y)
 -‵[ false ]· x y = RT'.-DistL· _ _
 -‵[ true ]· x y = refl
 
 _mb·‵_ : Maybe ⟨R'⟩ → ⟨R'⟩ → ⟨R'⟩
 nothing mb·‵ y = y
 just x mb·‵ y = x ·‵ y


 evPolynomialTerm : ∀ {n} → PolynomialTerm n → Vec ⟨R'⟩ n → ⟨R'⟩
 evPolynomialTerm (b , mbK , m) xs = -‵[ b ] (Mb.fromJust-def 1r‵
   (map-Maybe (fst hom) mbK mb·‵mb evMonomial m xs))

 Polynomial : ℕ → Type ℓ
 Polynomial n = List (PolynomialTerm n)

 evPolynomial :  ∀ {n} → Polynomial n → Vec ⟨R'⟩ n → ⟨R'⟩
 evPolynomial [] vs = 0r‵
 evPolynomial P[ x ] vs = evPolynomialTerm x vs
 evPolynomial (x ∷ xs@(_ ∷ _)) vs = evPolynomial xs vs +‵ evPolynomialTerm x vs

 
 Poly·X : ∀ {n} → Polynomial (ℕ.suc n) → Polynomial (ℕ.suc n) 
 Poly·X {n} = L.map (map-snd (map-snd λ { (x ∷ xs) → ℕ.suc x ∷ xs  }))

 Poly↑ : ∀ {n} → Polynomial n → Polynomial (ℕ.suc n) 
 Poly↑ {n} = L.map (map-snd (map-snd (ℕ.zero ∷_)))

 evPolynomial∷ : ∀ {n} t p vs → evPolynomial {n = n} (t ∷ p) vs
                         ≡ evPolynomial p vs +‵ evPolynomialTerm t vs   
 evPolynomial∷ t [] vs = sym (R‵.+IdL _)
 evPolynomial∷ t (x ∷ p) vs = refl
 
 evPolynomial++ : ∀ {n} p₀ p₁ vs → evPolynomial {n = n} (p₀ L.++ p₁) vs
                         ≡ evPolynomial p₁ vs +‵ evPolynomial p₀ vs 
 evPolynomial++ [] p₁ vs = sym (R‵.+IdR _)
 evPolynomial++ (x ∷ p₀) p₁ vs =
      evPolynomial∷ x (p₀ L.++ p₁) vs
   ∙∙ cong (_+‵ _) (evPolynomial++ p₀ p₁ vs)
      ∙ sym (R‵.+Assoc _ _ _)  
   ∙∙ cong (evPolynomial p₁ vs +‵_) (sym (evPolynomial∷ x p₀ vs)  )

 evMonomial·X : ∀ n m ms v vs → evMonomial {ℕ.suc n} (ℕ.suc m ∷ ms) (v ∷ vs)
                             ≡ (evMonomial {ℕ.suc n} (m ∷ ms) (v ∷ vs) mb·‵mb just v)
 evMonomial·X n m ms v vs =
      evMonomial∷ (ℕ.suc m) ms v vs
      ∙∙ hlp (evMonomial ms vs) m
   ∙∙ cong (_mb·‵mb just v) (sym (evMonomial∷ m ms v vs))
  where
   


   hlp : ∀ u m → (u mb·‵mb (v ^'' ℕ.suc m)) ≡
      ((u mb·‵mb (v ^'' m)) mb·‵mb just v)
   hlp nothing ℕ.zero = refl
   hlp nothing one = refl
   hlp nothing (ℕ.suc (ℕ.suc m)) = cong just (R‵.·Comm _ _)
   hlp (just x) ℕ.zero = refl
   hlp (just x) one = cong just (R‵.·Assoc _ _ _ )
   hlp (just x) (ℕ.suc (ℕ.suc m)) = cong just (cong (x ·‵_) (R‵.·Comm _ _) ∙ R‵.·Assoc _ _ _)
    
   
 evPolynomial·X : ∀ {n} p v vs →
      evPolynomial (Poly·X {n} p) (v ∷ vs) ≡
      evPolynomial p (v ∷ vs) ·‵ v
 evPolynomial·X [] v vs = sym (RT'.0LeftAnnihilates _)
 evPolynomial·X {n} (x@(b , k , m ∷ ms) ∷ p) v vs =
      evPolynomial∷ _ (Poly·X p) (v ∷ vs)
    ∙∙ cong₂ _+‵_
        (evPolynomial·X p v vs)
        (cong -‵[ b ] (
                (cong (λ u → fromJust-def 1r‵ ((map-Maybe (fst hom) k) mb·‵mb u))
                 (evMonomial·X n m ms v vs) ∙
                  hlp (evMonomial (m ∷ ms) (v ∷ vs)) (map-Maybe (fst hom) k))
             ∙ sym (∘fromJust-def (_·‵ v) 1r‵
              ((map-Maybe (fst hom) k) mb·‵mb evMonomial (m ∷ ms) (v ∷ vs))))
           ∙ sym (-‵[ b ]· _ _))
    ∙∙ sym (R‵.·DistL+ _ _ v)
      ∙ cong (_·‵ v) (sym (evPolynomial∷ _ p _))
  where
  hlp : ∀ u k → fromJust-def 1r‵ (k mb·‵mb (u mb·‵mb just v))
              ≡ fromJust-def (1r‵ ·‵ v) (map-Maybe (_·‵ v) (k mb·‵mb u))
  hlp nothing nothing = sym (R‵.·IdL _)
  hlp nothing (just x) = refl
  hlp (just x) nothing = refl
  hlp (just x) (just x₁) = R‵.·Assoc _ _ _
     
 evPolynomial↑ : ∀ {n} p v vs →
                    evPolynomial (Poly↑ p) (v ∷ vs) ≡
                     evPolynomial {n = n} p (vs)
 evPolynomial↑ [] v vs = refl
 evPolynomial↑ (x ∷ p) v vs =
       evPolynomial∷ _ (Poly↑ p) (v ∷ vs)
    ∙∙ cong₂ _+‵_ (evPolynomial↑ p v vs)
        (cong (-‵[ x .fst ] ∘ fromJust-def 1r‵ ∘ (map-Maybe (fst hom) (x .snd .fst)) mb·‵mb_)
          (   evMonomial∷ _ _ v vs
           ∙ mb·‵mbIdR _))
    ∙∙ sym (evPolynomial∷ _ p vs)

 Horner→Poly : ∀ {n} → Maybe (Discrete ⟨R⟩) →  (h : IteratedHornerForms n)
                     → Σ (Polynomial n) λ pf → ∀ xs → evPolynomial pf xs ≡ eval h xs 
 Horner→Poly nothing (const x) = [ true , (just x) , [] ] , λ {[] → refl}
 Horner→Poly (just _≟_) (const x) = hlp (x ≟ 0r) (x ≟ 1r) (x ≟ (- 1r))
  where
  hlp : Dec _ →  Dec _ → Dec _ → _
  hlp (yes x≡0) _ _ = [] , λ {[] → sym (IsCommRingHom.pres0 (snd hom)) ∙ cong (hom .fst) (sym x≡0) }
  hlp _ (yes x≡1) x₁ =
    [ true , nothing , [] ] , λ {[] → sym (IsCommRingHom.pres1 (snd hom)) ∙ cong (hom .fst) (sym x≡1)}
  hlp _ (no ¬p) (yes x≡-1) =
    [ false , nothing , [] ] , λ {[] → sym (IsCommRingHom.pres- (snd hom) 1r
      ∙ cong -‵_ (IsCommRingHom.pres1 (snd hom))) ∙ cong (hom .fst) (sym x≡-1)}
  hlp _ (no ¬p) (no ¬p₁) = [ true , (just x) , [] ] , λ {[] → refl}

 Horner→Poly _ 0H = [] , λ _ → refl
 Horner→Poly mbD (h₀ ·X+ h₁) =
  let p₀ , q₀ = Horner→Poly mbD h₀
      p₁ , q₁ = Horner→Poly mbD h₁
  in Poly·X p₀ L.++ Poly↑ p₁ , λ { vvs@(v ∷ vs) →
          evPolynomial++ (Poly·X p₀) (Poly↑ p₁) vvs
       ∙ R‵.+Comm _ _ ∙ cong₂ _+‵_
          (evPolynomial·X p₀ v vs ∙ cong (_·‵ v) (q₀ (v ∷ vs)))
          (evPolynomial↑ p₁ v vs ∙ q₁ vs)}


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

 ×[_]ᵗʸ : List (Type ℓ) → Type ℓ
 ×[_]ᵗʸ = RepListP (idfun _)

  
 [X]? : ∀ {ℓ'} → Type ℓ'  → Type (ℓ-max (ℓ-suc ℓ) ℓ')
 [X]? A = (Σ (List (Type ℓ)) (λ XS → (([ XS ]ᵗʸ → A) ×
               (ListP (λ X → Discrete ⟨R⟩ → Maybe X) XS))))

 ×-[X]? : ∀ {ℓ'} → {A A' : Type ℓ'} → [X]? A → [X]? A' → [X]? (A × A')
 ×-[X]? (XS , f , d) (XS' , f' , d') =
   XS L.++ XS' , (map-× f f') ∘S splitP {xs = XS} {XS'} , (d ++P d')
 
 map-[X]? : ∀ {ℓ'} → {A A' : Type ℓ'} → (A → A')
           → [X]? A → [X]? A' 
 map-[X]? f = map-snd (map-fst (f ∘S_))
 

 IHR?0 : ∀ {n} → ∀ (e : IteratedHornerForms n) →
           [X]?  (e ≑ 0ₕ) 
 IHR?0 (const x) = 
    ([ x ≡ 0r ]) , (λ { (p ∷ []) [] → cong (hom .fst) p} )
    , ((λ _≟_ → decRec just (λ _ → nothing) (x ≟ 0r)) ∷ [])
 IHR?0 0H = [] , (λ _ xs → Eval0H xs) , [] 
 IHR?0 (e ·X+ e₁) =
   map-[X]?
     (λ (f , f') → λ {(v ∷ vs) →
      cong₂ R‵._+_
           (RT'.0LeftAnnihilates'  _ _  (f (v ∷ vs)))
           (f' vs) ∙ RT'.+IdR' _ _ (Eval0H vs) })
     (×-[X]? (IHR?0 e) (IHR?0 e₁))

   
 IHR? : ∀ {n} → ∀ (e₁ e₂ : IteratedHornerForms n) →
     [X]? (e₁ ≑ e₂)
 IHR? (const x) (const x') = [ x ≡ x' ] , (( λ { (p ∷ []) [] → cong (hom .fst) p }) ,
   (λ _≟_ → decToMaybe (x ≟ x')) ∷ [])
 IHR? 0H e = map-[X]?
  (λ f → λ { (v ∷ vs) → sym   (f (v ∷ vs)) }) (IHR?0 e)
 IHR? e 0H =
    map-[X]?
  (λ f → λ { (v ∷ vs) → (f (v ∷ vs)) }) (IHR?0 e)
 IHR? (e ·X+ e₁) (e' ·X+ e₁') =
  map-[X]?
    ((λ (f , f') → λ {(v ∷ vs) →
       cong₂ R‵._+_ (cong (_·‵ v)  (f (v ∷ vs))) (f' vs)}))
    (×-[X]? (IHR? e e') (IHR? e₁ e₁'))  


 

  
 IHR?-refl : ∀ {n} → ∀ (e : IteratedHornerForms n) → [ fst (IHR? e e) ]ᵗʸ
 IHR?-refl (const x) = refl ∷ []
 IHR?-refl 0H = []
 IHR?-refl (e ·X+ e₁) = IHR?-refl e ++P IHR?-refl e₁



 solve :
   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
   → [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 solve e₁ e₂ xs z =
   ⟦ e₁ ⟧ xs               ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
   eval (normalize e₁) xs ≡⟨ (fst (snd (IHR? (normalize e₁) (normalize e₂))) z xs) ⟩
   eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
   ⟦ e₂ ⟧ xs ∎

 solveByDec :
   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n) 
   → [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ
        ⁇→ (⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs)
 solveByDec e₁ e₂ xs = ⁇λ solve e₁ e₂ xs

 IsConst : ∀ {n} → IteratedHornerForms n → Type (ℓ-suc ℓ)
 IsConst (const x) = Unit* 
 IsConst 0H = ⊥*
 IsConst (P ·X+ Q) = [ fst (IHR?0 P)  ]ᵗʸ × IsConst Q

 IsConst→ev : ∀ {n} e → IsConst {n} e → Σ[ a ∈ ⟨R⟩ ] (∀ xs → eval e xs ≡ fst hom a )
 IsConst→ev (const a) _ = a , λ { [] → refl }
 IsConst→ev (P ·X+ Q) (u , v) =
  let (a , p) = IsConst→ev Q v
  in a , λ { (x ∷ xs) → RT'.+IdL' _ _
    (RT'.0LeftAnnihilates'  _ _ (fst (snd (IHR?0 P)) u (x ∷ xs)))
     ∙ p xs }
     
 HeadVarMonomial : ∀ {n} → IteratedHornerForms (ℕ.suc n) → Type (ℓ-suc ℓ)
 HeadVarMonomial 0H = ⊥*
 HeadVarMonomial {n} x@(P ·X+ Q) =
   (HeadVarMonomial P × [ fst (IHR?0 Q)  ]ᵗʸ) ⊎ IsConst x

 
 record Elimination {n : ℕ} (P : IteratedHornerForms (ℕ.suc n)) (iX : Fin (ℕ.suc n)) : Type (ℓ-max ℓ' ℓ) where 
  field
   k : ℕ₊₁
   a : ⟨R⟩ 
   Q : IteratedHornerForms n
   a·xᵏ≡p : ∀ xs b → eval P xs ≡ b → (fst hom a) ·‵
       (lookup iX xs ^ ℕ₊₁→ℕ k) +‵ b ≡ eval Q (drop iX xs)



 IsolatedPowerHeadVar : ∀ {n} → IteratedHornerForms (ℕ.suc n) → Type (ℓ-suc ℓ)
 IsolatedPowerHeadVar 0H = ⊥*
 IsolatedPowerHeadVar (P ·X+ Q) =
   HeadVarMonomial P


 toElimination : ∀ {n} P → (IsolatedPowerHeadVar P) → Elimination {n} P zero
 toElimination (P ·X+ Q) hvm = 
   let ((k , a) , eqtion) = h P hvm
   in record { k = 1+ k
             ; a = a
             ; Q = Q
             ; a·xᵏ≡p = λ { (x ∷ xs) b p →
                cong (_+‵ b) (((cong (fst hom a ·‵_) (R‵.·Comm _ _)
                  ∙ R‵.·Assoc _ _ _)
                 ∙ cong (_·‵ x) (eqtion x xs))
                 ∙ RT'.-DistL· _ _) ∙ R‵.+Comm _ _
                  ∙  (cong (_-‵ (eval P (x ∷ xs) ·‵ x)) (sym p ∙ (R‵.+Comm _ _)))
                   ∙ RT'.plusMinus _ _ } }
  where
  h : ∀ {n} e → HeadVarMonomial {n} e →
        Σ (ℕ × ⟨R⟩)
          λ (k , a) → ∀ x xs → (fst hom a) ·‵ (x ^ k) ≡ -‵ (eval e (x ∷ xs))  
  h (e ·X+ e₁) =
    ⊎.rec
     (λ (u , v) →
       let ((k , a) , eqtion) = h e u 
       in (ℕ.suc k , a) , λ x xs →
              (cong ((fst hom a) ·‵_) (R‵.·Comm _ _)
              ∙ R‵.·Assoc _ _ _)
            ∙∙ cong (_·‵ x) (eqtion x xs)
            ∙∙ (RT'.-DistL· _ _
             ∙ cong -‵_ (sym (RT'.+IdR' _ _ (fst (snd (IHR?0 e₁)) v xs ∙ Eval0H xs )))))
     λ (u , v) →
       let (a , p) = IsConst→ev e₁ v
       in (0 , (- a)) , λ x xs →
            R‵.·IdR _
          ∙∙ IsCommRingHom.pres- (snd hom) a
          ∙∙ cong -‵_ (sym (p xs)
             ∙ sym (RT'.+IdL' _ _ (RT'.0LeftAnnihilates' _ _ (fst (snd (IHR?0 e)) u (x ∷ xs)) )))
  
 FreeOfVar : ∀ {n} → IteratedHornerForms n → Fin n → Type (ℓ-suc ℓ) 
 FreeOfVar 0H _ = Unit*
 FreeOfVar (P ·X+ Q) zero = [ fst (IHR?0 P)  ]ᵗʸ
 FreeOfVar (P ·X+ Q) (suc k) = FreeOfVar P (suc k) × FreeOfVar Q k

 FreeOfVar→ev : ∀ {n} P k → FreeOfVar {ℕ.suc n} P k
    → Σ[ P' ∈ IteratedHornerForms n ] (∀ xs → eval P xs ≡ eval P' (Vec.drop k xs) )
 FreeOfVar→ev 0H k _ = 0ₕ , λ xs → sym (Eval0H (Vec.drop k xs))
   
 FreeOfVar→ev (P ·X+ Q) zero u = Q ,
   λ { (x ∷ xs) → RT'.+IdL' _ _ (RT'.0LeftAnnihilates' _ _
     ((fst (snd (IHR?0 P)) u (x ∷ xs)))) }
 FreeOfVar→ev {ℕ.suc n} (P HornerForms.·X+ Q) (suc k) (p , q) =
   let (P' , p') = FreeOfVar→ev P (suc k) p 
       (Q' , q') = FreeOfVar→ev Q k q
   in (P' ·X+ Q') , λ { (x ∷ xs) →
     cong₂ _+‵_ (cong (_·‵ x) (p' (x ∷ xs))) (q' xs) }


 IsolatedPowerVar : ∀ {n} → IteratedHornerForms n → Fin n → Type (ℓ-suc ℓ)
 IsolatedPowerVar {ℕ.suc n} 0H _ = ⊥*
 IsolatedPowerVar {ℕ.suc n} (P ·X+ Q) zero =
   HeadVarMonomial P
 IsolatedPowerVar {ℕ.suc n} (P ·X+ Q) (suc k) =
   FreeOfVar P (suc k) × IsolatedPowerVar Q k


 IsolatedPowerVar→ev : ∀ {n} P → ∀ k →  IsolatedPowerVar {ℕ.suc n} P k
    → Elimination P k
 IsolatedPowerVar→ev {n} P@(_ ·X+ _) zero = toElimination P 
 IsolatedPowerVar→ev {ℕ.suc n} (P ·X+ R) (suc m) (p , r) =
   let (P' , p') = FreeOfVar→ev P (suc m) p
        
   in record {  k = k ; a = a ; Q = P' ·X+ Q ;
        a·xᵏ≡p = λ { xss@(x ∷ xs) b p →
          let zz = p' xss
              zz' = a·xᵏ≡p xs (b -‵ eval P (x ∷ xs) ·‵ x)
                        (sym (RT'.plusMinus _ _) ∙
                         cong (_-‵ (eval P (x ∷ xs) ·‵ x)) (R‵.+Comm _ _ ∙ p))
              zz'' = cong₂ _+‵_ (cong (_·‵ x) (p' xss))
                     (zz')
          in sym (RT'.minusPlus _ _)
              ∙ R‵.+Comm _ _ ∙ cong₂ _+‵_ refl (sym (R‵.+Assoc _ _ _)) ∙ zz''
         }}
   where 
   open Elimination (IsolatedPowerVar→ev R m r)

 
 module Decidable (_≟_ : Discrete ⟨R⟩) where

  

  HF-Maybe-prfₕ : {n : ℕ} (e₁ e₂ : IteratedHornerForms n) 
                   → Maybe [ fst (IHR? e₁ e₂) ]ᵗʸ
  HF-Maybe-prfₕ e₁ e₂ =
   sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR? e₁ e₂))))


  HF-Maybe-prf : {n : ℕ} (e₁ e₂ : RExpr n) 
                   → Maybe [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ
  HF-Maybe-prf e₁ e₂ = HF-Maybe-prfₕ (normalize e₁) (normalize e₂)

  mbIsConst : {n : ℕ}
        → (e : IteratedHornerForms n)
        → Maybe (IsConst e)
  mbIsConst (const _) = just _
  mbIsConst 0H = nothing
  mbIsConst (P ·X+ Q) =
    ⦇ (sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR?0 P)))))
    , (mbIsConst Q) ⦈
  
  mbHeadVarMonomial : {n : ℕ}
        → (e : IteratedHornerForms (ℕ.suc n))
        → Maybe (HeadVarMonomial e)
  mbHeadVarMonomial 0H = nothing
  mbHeadVarMonomial P+Q@(P ·X+ Q) =
    Mb.rec (map-Maybe inl
        ⦇ mbHeadVarMonomial P , (sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR?0 Q))))) ⦈)
      (just ∘ inr)
      (mbIsConst P+Q)


  mbIsolatedPowerHeadVar : {n : ℕ}
        → (e : IteratedHornerForms (ℕ.suc n))
        → Maybe (IsolatedPowerHeadVar e)
  mbIsolatedPowerHeadVar 0H = nothing
  mbIsolatedPowerHeadVar {n} (P ·X+ Q) = mbHeadVarMonomial P

  mbFreeOfVar : ∀ {n} P k → Maybe (FreeOfVar {n} P k)
  mbFreeOfVar 0H k = just _
  mbFreeOfVar (P ·X+ Q) zero =
   sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR?0 P)))) 
  mbFreeOfVar (P ·X+ Q) (suc k) =
    ⦇ (mbFreeOfVar P (suc k)) , (mbFreeOfVar Q k) ⦈
  
  mbIsolatedPowerVar : ∀ {n} P k → Maybe (IsolatedPowerVar {n} P k)
  mbIsolatedPowerVar {ℕ.suc n} HornerForms.0H zero = nothing
  mbIsolatedPowerVar {ℕ.suc n} P@(_ ·X+ _) zero = mbIsolatedPowerHeadVar P
  mbIsolatedPowerVar {ℕ.suc n} 0H (suc k) = nothing
  mbIsolatedPowerVar {ℕ.suc n} (P ·X+ Q) (suc k) =
    ⦇ (mbFreeOfVar P (suc k)) , (mbIsolatedPowerVar Q k) ⦈
    
  normalizeIHF' : ∀ {n} → (e : IteratedHornerForms n) → ((e ≑ 0ₕ) ⊎ Σ _ (e ≑_ ))
  normalizeIHF'  (const x) =
     decRec (λ x≡0 → inl λ xs i → eval (HornerForms.const (x≡0 i)) xs)
      (λ _ → inr (HornerForms.const x , λ _ → refl)) (x ≟ 0r)
  normalizeIHF' 0H = inl λ _ → refl
  normalizeIHF' e@(e₀ ·X+ e₁) = h (normalizeIHF' e₀) (normalizeIHF' e₁)
    where
    h : ((e₀ ≑ 0ₕ) ⊎ Σ _ (e₀ ≑_ )) → ((e₁ ≑ 0ₕ) ⊎ Σ _ (e₁ ≑_ )) → ((e ≑ 0ₕ) ⊎ Σ _ (e ≑_ ))
    h (inl x₀) (inl x₁) = inl λ { (v ∷ vs) →
       cong₂ R‵._+_
           (RT'.0LeftAnnihilates'  _ _  (x₀ (v ∷ vs)))
           (x₁ vs) ∙ RT'.+IdR' _ _ (Eval0H vs) }
    h x₀ x₁ =
      let (u₀ , y₀) = ⊎.rec (0ₕ ,_) (idfun _) x₀
          (u₁ , y₁) = ⊎.rec (0ₕ ,_) (idfun _) x₁
      in inr (u₀ ·X+ u₁ , λ { (v ∷ vs) i → y₀ (v ∷ vs) i ·‵ v +‵ y₁ vs i })
    

  normalizeIHF : ∀ {n} → (e : IteratedHornerForms n) → Σ _ (e ≑_ )
  normalizeIHF = ⊎.rec (0ₕ ,_) (idfun _) ∘ normalizeIHF'

  
  eval' : {n : ℕ} (P : IteratedHornerForms n)
         → (xs : Vec ⟨R'⟩ n) → Σ ⟨R'⟩ (_≡ eval P xs )
  eval' (const x) xs = _ , refl
  eval' 0H xs = _ , refl
  eval' P@(e₀ ·X+ e₁) vvs@(v ∷ vs) =
    h (normalizeIHF' e₀) (normalizeIHF' e₁)
   where


    ₕ·‵ : Σ ⟨R'⟩ (_≡ fst (eval' e₀ vvs) ·‵ v )
    ₕ·‵ with HF-Maybe-prfₕ e₀ (1ₕ) | HF-Maybe-prfₕ e₀ (-ₕ 1ₕ) 
    ... | nothing | nothing = _ , refl
    ... | just x | _ = v , sym (RT'.·IdL' _ _
       ((snd (eval' e₀ vvs)) ∙∙ (fst (snd (IHR? e₀ (1ₕ))) x vvs) ∙∙
        Eval1ₕ vvs))
    ... | _ | just x = -‵ v , sym (RT'.·IdL' _ _
       (cong -‵_ (((snd (eval' e₀ vvs)) ∙∙ (fst (snd (IHR? e₀ (-ₕ 1ₕ))) x vvs) ∙∙
          (-EvalDist 1ₕ vvs ∙ cong -‵_ (Eval1ₕ vvs))))
        ∙ RT'.-Idempotent _))
     ∙ RT'.-Dist· _ _ 

     


    h : ((e₀ ≑ 0ₕ) ⊎ Σ _ (e₀ ≑_ )) → ((e₁ ≑ 0ₕ) ⊎ Σ _ (e₁ ≑_ )) → Σ ⟨R'⟩ (_≡ eval P vvs )
    h (inl x₀) (inl x₁) =  0r‵ , 
            sym (RT'.0LeftAnnihilates'  _ _  (x₀ vvs))
        ∙ sym (RT'.+IdR' _ _ (x₁ vs ∙ Eval0H vs))
    h x₀@(inr _) (inl x₁) =  _ ,
      snd ₕ·‵ ∙ cong (_·‵ v) (snd (eval' e₀ vvs))
        ∙ sym (RT'.+IdR' _ _ (x₁ vs ∙ Eval0H vs))
    h (inl x₁) (inr x) = _ , snd (eval' e₁ vs) ∙ sym (RT'.+IdL' _ _
       (RT'.0LeftAnnihilates'  _ _  (x₁ vvs)))
    h (inr x₁) (inr x) = _ , cong₂ _+‵_
      (snd ₕ·‵ ∙ cong (_·‵ v) (snd (eval' e₀ vvs)))
      (snd (eval' e₁ vs))


  normalizeByDec :
    {n : ℕ} (e : RExpr n) (xs : Vec (fst R') n) 
    →  Σ _ (⟦ e ⟧ xs ≡_)
  normalizeByDec e xs = evPolynomial
                         (Horner→Poly (just _≟_) (fst (normalizeIHF (normalize e))) .fst) xs ,
        sym (isEqualToNormalform e xs)
     ∙∙ snd (normalizeIHF (normalize e)) xs
     ∙∙ sym ((Horner→Poly (just _≟_) (fst (normalizeIHF (normalize e))) . snd) xs)


  pickEliminations : {n : ℕ} (e₁ e₂ : RExpr (ℕ.suc n)) (xs : Vec (fst R') (ℕ.suc n)) →
    Vec (Maybe ℕ) (ℕ.suc n)
  pickEliminations e₁ e₂ xs =
    let (ihf , u) = normalizeIHF (normalize (e₁ +' -' e₂))
    in tabulate (λ k →
          map-Maybe (ℕ₊₁→ℕ ∘ Elimination.k ∘ IsolatedPowerVar→ev ihf k ) (mbIsolatedPowerVar ihf k))


  solveByDifference :  {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
     → fst (eval' (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) xs) ≡ 0r‵ → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  solveByDifference e₁ e₂ xs ev=0 =
      RT'.equalByDifference _ _ $ 
         cong₂ _+‵_ (sym (isEqualToNormalform e₁ xs))
          (cong -‵_ (sym (isEqualToNormalform e₂ xs)) ∙ sym (-EvalDist (normalize e₂) xs))
          ∙ sym (+Homeval (normalize e₁) (-ₕ (normalize e₂)) xs) ∙
            snd (normalizeIHF (normalize (e₁ +' -' e₂))) xs ∙
             sym (snd (eval' (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) xs)) ∙ ev=0


  solveByDifference' :  {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
     → evPolynomial (Horner→Poly (just _≟_)
      (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) . fst) xs
       ≡ 0r‵ → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  solveByDifference' e₁ e₂ xs ev=0 = 
      RT'.equalByDifference _ _ $ 
         cong₂ _+‵_ (sym (isEqualToNormalform e₁ xs))
          (cong -‵_ (sym (isEqualToNormalform e₂ xs)) ∙ sym (-EvalDist (normalize e₂) xs))
          ∙ sym (+Homeval (normalize e₁) (-ₕ (normalize e₂)) xs) ∙
              (snd (normalizeIHF (normalize (e₁ +' -' e₂))) xs)
             ∙ sym ((Horner→Poly (just _≟_)
              (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) . snd) xs) ∙ ev=0



-- 

 -- congSolve :
 --   {n : ℕ} (e₁ e₂ : RExpr n) → ∀ {xs xs' : Vec (fst R') n} → xs ≡ xs'
 --   → fst (IHR? (normalize e₁) (normalize e₂)) → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs'
 -- congSolve e₁ e₂ {xs} {xs'} p z =
 --   ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
 --   eval (normalize e₁) xs ≡⟨
 --    cong₂ eval (fst (snd (IHR? (normalize e₁) (normalize e₂))) z) p ⟩
 --   eval (normalize e₂) xs' ≡⟨ isEqualToNormalform e₂ xs' ⟩
 --   ⟦ e₂ ⟧ xs' ∎

 -- solveByPath :
 --   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
 --   → eval (normalize e₁) xs ≡ eval (normalize e₂) xs → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 -- solveByPath e₁ e₂ xs p =
 --    ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
 --    eval (normalize e₁) xs ≡⟨ p ⟩
 --    eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
 --    ⟦ e₂ ⟧ xs ∎
