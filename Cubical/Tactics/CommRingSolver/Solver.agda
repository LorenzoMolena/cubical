module Cubical.Tactics.CommRingSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ;suc;zero)
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

 open Exponentiation R' using (_^_)


 infix 9 _^'_

 _^'_ : ⟨R'⟩ → ℕ → ⟨R'⟩
 f ^' zero = 1r‵
 f ^' suc zero = f
 f ^' n@(suc (suc _)) = (f ^ n)

 ^'≡^ : ∀ x k → x ^' k ≡  x ^ k
 ^'≡^ x zero = refl
 ^'≡^ x (suc zero) = sym (R‵.·IdR _)
 ^'≡^ x (suc (suc k)) = refl


 -- module EvalPoly where
 --  open Sum (CommRing→Ring R')

 _^''_ : ⟨R'⟩ → ℕ → Maybe ⟨R'⟩
 x ^'' zero = nothing
 x ^'' suc zero = just x
 x ^'' suc n = just (x ^' (suc n) )

 ^''-suc : ∀ m v → v ^' suc m ≡ v ^' m ·‵ v
 ^''-suc zero v = sym (R‵.·IdL _)
 ^''-suc one v = cong (v ·‵_) (R‵.·IdR _)
 ^''-suc (suc (suc m)) v = R‵.·Comm _ _

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
 evMonomial {n = suc (suc _)} (m ∷ xs) (v ∷ vs) = (evMonomial xs vs) mb·‵mb (v ^'' m)

 evMonomial∷ : ∀ {n} m ms v vs → evMonomial {suc n} (m ∷ ms) (v ∷ vs) ≡
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



 evPolynomialTerm' : ∀ {n} → PolynomialTerm n → Vec ⟨R'⟩ n → ⟨R'⟩
 evPolynomialTerm' (_ , mbK , m) xs =  (Mb.fromJust-def 1r‵
   (map-Maybe (fst hom) mbK mb·‵mb evMonomial m xs))


 evPolynomialTerm : ∀ {n} → PolynomialTerm n → Vec ⟨R'⟩ n → ⟨R'⟩
 evPolynomialTerm (b , mbK , m) xs = -‵[ b ] (evPolynomialTerm' (b , mbK , m) xs)


 Polynomial : ℕ → Type ℓ
 Polynomial n = List (PolynomialTerm n)

 evPolynomial :  ∀ {n} → Polynomial n → Vec ⟨R'⟩ n → ⟨R'⟩
 evPolynomial [] vs = 0r‵
 evPolynomial P[ x ] vs = evPolynomialTerm x vs
 evPolynomial (x@(false , mbK , m) ∷ xs@(_ ∷ _)) vs =
  evPolynomial xs vs -‵ evPolynomialTerm' x vs
 evPolynomial (x@(true , mbK , m) ∷ xs@(_ ∷ _)) vs =
  evPolynomial xs vs +‵ evPolynomialTerm' x vs

 
 Poly·X : ∀ {n} → Polynomial (suc n) → Polynomial (suc n) 
 Poly·X {n} = L.map (map-snd (map-snd λ { (x ∷ xs) → suc x ∷ xs  }))

 Poly↑ : ∀ {n} → Polynomial n → Polynomial (suc n) 
 Poly↑ {n} = L.map (map-snd (map-snd (zero ∷_)))

 evPolynomial∷ : ∀ {n} t p vs → evPolynomial {n = n} (t ∷ p) vs
                         ≡ evPolynomial p vs +‵ evPolynomialTerm t vs   
 evPolynomial∷ t [] vs = sym (R‵.+IdL _)
 evPolynomial∷ (false , _) (x ∷ p) vs = refl
 evPolynomial∷ (true , _) (x ∷ p) vs = refl
 
 evPolynomial++ : ∀ {n} p₀ p₁ vs → evPolynomial {n = n} (p₀ L.++ p₁) vs
                         ≡ evPolynomial p₁ vs +‵ evPolynomial p₀ vs 
 evPolynomial++ [] p₁ vs = sym (R‵.+IdR _)
 evPolynomial++ (x ∷ p₀) p₁ vs =
      evPolynomial∷ x (p₀ L.++ p₁) vs
   ∙∙ cong (_+‵ _) (evPolynomial++ p₀ p₁ vs)
      ∙ sym (R‵.+Assoc _ _ _)  
   ∙∙ cong (evPolynomial p₁ vs +‵_) (sym (evPolynomial∷ x p₀ vs)  )

 evMonomial·X : ∀ n m ms v vs → evMonomial {suc n} (suc m ∷ ms) (v ∷ vs)
                             ≡ (evMonomial {suc n} (m ∷ ms) (v ∷ vs) mb·‵mb just v)
 evMonomial·X n m ms v vs =
      evMonomial∷ (suc m) ms v vs
      ∙∙ hlp (evMonomial ms vs) m
   ∙∙ cong (_mb·‵mb just v) (sym (evMonomial∷ m ms v vs))
  where
   


   hlp : ∀ u m → (u mb·‵mb (v ^'' suc m)) ≡
      ((u mb·‵mb (v ^'' m)) mb·‵mb just v)
   hlp nothing zero = refl
   hlp nothing one = cong just (cong (v ·‵_) (R‵.·IdR _))
   hlp nothing (suc (suc m)) = cong just (R‵.·Comm _ _)
   hlp (just x) zero = refl
   hlp (just x) one = cong just
     (cong (x ·‵_) (cong (v ·‵_) (R‵.·IdR _)) ∙ R‵.·Assoc _ _ _ )
   hlp (just x) (suc (suc m)) = cong just
     (cong (x ·‵_) (R‵.·Comm _ _) ∙ R‵.·Assoc _ _ _)
    
   
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

 -- PolynomialTerm· : ∀ {n} → PolynomialTerm n → PolynomialTerm n → PolynomialTerm n
 -- PolynomialTerm· = {!!}

 PolynomialTerm· : ∀ {n} → PolynomialTerm n → PolynomialTerm n → PolynomialTerm n
 PolynomialTerm· {n} (b₁ , k₁ , m₁) (b₂ , k₂ , m₂) =
   ( b₁ ⊙ b₂
   , k₁ mb·mb k₂
   , mon· m₁ m₂
   )
   where

   -- sign multiplication: false = “negated”, true = “unchanged”
   _⊙_ : Bool → Bool → Bool
   true  ⊙ b = b
   false ⊙ true  = false
   false ⊙ false = true

   -- Maybe-coefficient multiplication, with `nothing` = implicit 1
   _mb·mb_ : Maybe ⟨R⟩ → Maybe ⟨R⟩ → Maybe ⟨R⟩
   nothing mb·mb y = y
   just x  mb·mb y = just (Mb.rec x (x ·_) y)

   -- Monomial multiplication = add exponents pointwise
   mon· : ∀ {n} → Monomial n → Monomial n → Monomial n
   mon· [] [] = []
   mon· (e ∷ es) (f ∷ fs) = (ℕ._+_ e f) ∷ mon· es fs

--  RExpr : (n : ℕ) → Type _
--  RExpr = Expr RRng (fst R')

--  normalize : {n : ℕ} → RExpr n → IteratedHornerForms n
--  normalize {n = n} (K r) = Constant n r
--  normalize {n = n} (∣ k) = Variable n k
--  normalize (x +' y) =
--    (normalize x) +ₕ (normalize y)
--  normalize (x ·' y) =
--    (normalize x) ·ₕ (normalize y)
--  normalize (-' x) =  -ₕ (normalize x)

--  evalConstant : ∀ n r xs → eval (Constant n r) xs ≡ hom .fst r
--  evalConstant zero r [] = refl
--  evalConstant (suc n) r (x ∷ xs) =
--    RT'.+IdL' _ _ (RT'.0LeftAnnihilates _)
--       ∙ evalConstant n r xs 
 
--  isEqualToNormalform :
--       {n : ℕ} (e : RExpr n) (xs : Vec (fst R') n)
--     → eval (normalize e) xs ≡ ⟦ e ⟧ xs


--  isEqualToNormalform {n = n} (K r) xs = evalConstant n r xs

--  isEqualToNormalform (∣ zero) (x ∷ xs) = 
--    eval 1ₕ (x ∷ xs) ·‵ x +‵ eval 0ₕ xs   ≡⟨ cong (λ u → u ·‵ x +‵ eval 0ₕ xs)
--                                              (Eval1ₕ (x ∷ xs)) ⟩
--    1r‵ ·‵ x +‵ eval 0ₕ xs                 ≡⟨ cong (λ u → 1r‵  ·‵ x +‵ u ) (Eval0H xs) ⟩
--    1r‵ ·‵ x +‵ 0r‵                        ≡⟨ R‵.+IdR _ ⟩
--    1r‵ ·‵ x                             ≡⟨ R‵.·IdL _ ⟩
--    x ∎
--  isEqualToNormalform {n = suc n} (∣ (suc k)) (x ∷ xs) =
--      eval 0ₕ (x ∷ xs) ·‵ x +‵ eval (Variable n k) xs ≡⟨ cong (λ u → u ·‵ x +‵ eval (Variable n k) xs)
--                                                              (Eval0H (x ∷ xs)) ⟩
--      0r‵ ·‵ x +‵ eval (Variable n k) xs              ≡⟨ cong (λ u → u +‵ eval (Variable n k) xs)
--                                                              (R‵.0LeftAnnihilates _) ⟩
--      0r‵ +‵ eval (Variable n k) xs                  ≡⟨ R‵.+IdL _ ⟩
--      eval (Variable n k) xs                       ≡⟨ isEqualToNormalform (∣ k) xs ⟩
--      ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

--  isEqualToNormalform (-' e) [] =
--    eval (-ₕ (normalize e)) []  ≡⟨ -EvalDist (normalize e) [] ⟩
--    -‵ eval (normalize e) []    ≡⟨ cong -‵_ (isEqualToNormalform e [] ) ⟩
--    -‵ ⟦ e ⟧ [] ∎
--  isEqualToNormalform (-' e) (x ∷ xs) =
--    eval (-ₕ (normalize e)) (x ∷ xs) ≡⟨ -EvalDist (normalize e) (x ∷ xs) ⟩
--    -‵ eval (normalize e) (x ∷ xs)    ≡⟨ cong -‵_ (isEqualToNormalform e (x ∷ xs) ) ⟩
--    -‵ ⟦ e ⟧ (x ∷ xs) ∎

--  isEqualToNormalform (e +' e₁) [] =
--        eval (normalize e +ₕ normalize e₁) []
--      ≡⟨ +Homeval (normalize e) _ [] ⟩
--        eval (normalize e) []
--        +‵ eval (normalize e₁) []
--      ≡⟨ cong (λ u → u +‵ eval (normalize e₁) [])
--              (isEqualToNormalform e []) ⟩
--        ⟦ e ⟧ []
--        +‵ eval (normalize e₁) []
--      ≡⟨ cong (λ u → ⟦ e ⟧ [] +‵ u) (isEqualToNormalform e₁ []) ⟩
--        ⟦ e ⟧ [] +‵ ⟦ e₁ ⟧ [] ∎
--  isEqualToNormalform (e +' e₁) (x ∷ xs) =
--        eval (normalize e +ₕ normalize e₁) (x ∷ xs)
--      ≡⟨ +Homeval (normalize e) _ (x ∷ xs) ⟩
--        eval (normalize e) (x ∷ xs) +‵ eval (normalize e₁) (x ∷ xs)
--      ≡⟨ cong (λ u → u +‵ eval (normalize e₁) (x ∷ xs))
--              (isEqualToNormalform e (x ∷ xs)) ⟩
--        ⟦ e ⟧ (x ∷ xs) +‵ eval (normalize e₁) (x ∷ xs)
--      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) +‵ u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
--        ⟦ e ⟧ (x ∷ xs) +‵ ⟦ e₁ ⟧ (x ∷ xs) ∎

--  isEqualToNormalform (e ·' e₁) [] =
--        eval (normalize e ·ₕ normalize e₁) []
--      ≡⟨ ·Homeval (normalize e) _ [] ⟩
--        eval (normalize e) [] ·‵ eval (normalize e₁) []
--      ≡⟨ cong (λ u → u ·‵ eval (normalize e₁) [])
--              (isEqualToNormalform e []) ⟩
--        ⟦ e ⟧ [] ·‵ eval (normalize e₁) []
--      ≡⟨ cong (λ u → ⟦ e ⟧ [] ·‵ u) (isEqualToNormalform e₁ []) ⟩
--        ⟦ e ⟧ [] ·‵ ⟦ e₁ ⟧ [] ∎

--  isEqualToNormalform (e ·' e₁) (x ∷ xs) =
--        eval (normalize e ·ₕ normalize e₁) (x ∷ xs)
--      ≡⟨ ·Homeval (normalize e) _ (x ∷ xs) ⟩
--        eval (normalize e) (x ∷ xs) ·‵ eval (normalize e₁) (x ∷ xs)
--      ≡⟨ cong (λ u → u ·‵ eval (normalize e₁) (x ∷ xs))
--              (isEqualToNormalform e (x ∷ xs)) ⟩
--        ⟦ e ⟧ (x ∷ xs) ·‵ eval (normalize e₁) (x ∷ xs)
--      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) ·‵ u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
--        ⟦ e ⟧ (x ∷ xs) ·‵ ⟦ e₁ ⟧ (x ∷ xs) ∎


--  [_]ᵗʸ : List (Type ℓ) → Type (ℓ-suc ℓ)
--  [_]ᵗʸ = ListP (idfun _)

--  ×[_]ᵗʸ : List (Type ℓ) → Type ℓ
--  ×[_]ᵗʸ = RepListP (idfun _)

  
--  [X]? : ∀ {ℓ'} → Type ℓ'  → Type (ℓ-max (ℓ-suc ℓ) ℓ')
--  [X]? A = (Σ (List (Type ℓ)) (λ XS → (([ XS ]ᵗʸ → A) ×
--                (ListP (λ X → Discrete ⟨R⟩ → Maybe X) XS))))

--  ×-[X]? : ∀ {ℓ'} → {A A' : Type ℓ'} → [X]? A → [X]? A' → [X]? (A × A')
--  ×-[X]? (XS , f , d) (XS' , f' , d') =
--    XS L.++ XS' , (map-× f f') ∘S splitP {xs = XS} {XS'} , (d ++P d')
 
--  map-[X]? : ∀ {ℓ'} → {A A' : Type ℓ'} → (A → A')
--            → [X]? A → [X]? A' 
--  map-[X]? f = map-snd (map-fst (f ∘S_))
 

--  IHR?0 : ∀ {n} → ∀ (e : IteratedHornerForms n) →
--            [X]?  (e ≑ 0ₕ) 
--  IHR?0 (const x) = 
--     ([ x ≡ 0r ]) , (λ { (p ∷ []) [] → cong (hom .fst) p} )
--     , ((λ _≟_ → decRec just (λ _ → nothing) (x ≟ 0r)) ∷ [])
--  IHR?0 0H = [] , (λ _ xs → Eval0H xs) , [] 
--  IHR?0 (e ·X+ e₁) =
--    map-[X]?
--      (λ (f , f') → λ {(v ∷ vs) →
--       cong₂ R‵._+_
--            (RT'.0LeftAnnihilates'  _ _  (f (v ∷ vs)))
--            (f' vs) ∙ RT'.+IdR' _ _ (Eval0H vs) })
--      (×-[X]? (IHR?0 e) (IHR?0 e₁))

--  -- formIHR?0 : ∀ {n} P (Q : IteratedHornerForms n)  →
--  --              [ fst (IHR?0 (P ·X+ Q)) ]ᵗʸ →
--  --              [ fst (IHR?0 P) ]ᵗʸ
--  -- formIHR?0 = {!!}
 
--  IHR? : ∀ {n} → ∀ (e₁ e₂ : IteratedHornerForms n) →
--      [X]? (e₁ ≑ e₂)
--  IHR? (const x) (const x') = [ x ≡ x' ] , (( λ { (p ∷ []) [] → cong (hom .fst) p }) ,
--    (λ _≟_ → decToMaybe (x ≟ x')) ∷ [])
--  IHR? 0H e = map-[X]?
--   (λ f → λ { (v ∷ vs) → sym   (f (v ∷ vs)) }) (IHR?0 e)
--  IHR? e 0H =
--     map-[X]?
--   (λ f → λ { (v ∷ vs) → (f (v ∷ vs)) }) (IHR?0 e)
--  IHR? (e ·X+ e₁) (e' ·X+ e₁') =
--   map-[X]?
--     ((λ (f , f') → λ {(v ∷ vs) →
--        cong₂ R‵._+_ (cong (_·‵ v)  (f (v ∷ vs))) (f' vs)}))
--     (×-[X]? (IHR? e e') (IHR? e₁ e₁'))  


 

  
--  IHR?-refl : ∀ {n} → ∀ (e : IteratedHornerForms n) → [ fst (IHR? e e) ]ᵗʸ
--  IHR?-refl (const x) = refl ∷ []
--  IHR?-refl 0H = []
--  IHR?-refl (e ·X+ e₁) = IHR?-refl e ++P IHR?-refl e₁



--  solve :
--    {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
--    → [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
--  solve e₁ e₂ xs z =
--    ⟦ e₁ ⟧ xs               ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
--    eval (normalize e₁) xs ≡⟨ (fst (snd (IHR? (normalize e₁) (normalize e₂))) z xs) ⟩
--    eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
--    ⟦ e₂ ⟧ xs ∎

--  solveByDec :
--    {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n) 
--    → [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ
--         ⁇→ (⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs)
--  solveByDec e₁ e₂ xs = ⁇λ solve e₁ e₂ xs

--  IsConstPossiblyNonNull : ∀ {n} → IteratedHornerForms n → Type (ℓ-suc ℓ)
--  IsConstPossiblyNonNull (const x) = Unit* 
--  IsConstPossiblyNonNull 0H = ⊥*
--  IsConstPossiblyNonNull (P ·X+ Q) = [ fst (IHR?0 P)  ]ᵗʸ × IsConstPossiblyNonNull Q

--  IsConstPossiblyNonNull→ev : ∀ {n} e → IsConstPossiblyNonNull {n} e → Σ[ a ∈ ⟨R⟩ ] (∀ xs → eval e xs ≡ fst hom a )
--  IsConstPossiblyNonNull→ev (const a) _ = a , λ { [] → refl }
--  IsConstPossiblyNonNull→ev (P ·X+ Q) (u , v) =
--   let (a , p) = IsConstPossiblyNonNull→ev Q v
--   in a , λ { (x ∷ xs) → RT'.+IdL' _ _
--     (RT'.0LeftAnnihilates'  _ _ (fst (snd (IHR?0 P)) u (x ∷ xs)))
--      ∙ p xs }

--  --
--  FreeOfVar : ∀ {n} → IteratedHornerForms n → Fin n → Type (ℓ-suc ℓ) 
--  FreeOfVar 0H _ = Unit*
--  FreeOfVar (P ·X+ Q) zero = [ fst (IHR?0 P)  ]ᵗʸ
--  FreeOfVar (P ·X+ Q) (suc k) = FreeOfVar P (suc k) × FreeOfVar Q k

--  FreeOfVar→ev : ∀ {n} P k → FreeOfVar {suc n} P k
--     → Σ[ P' ∈ IteratedHornerForms n ] (∀ xs → eval P xs ≡ eval P' (Vec.drop k xs) )
--  FreeOfVar→ev 0H k _ = 0ₕ , λ xs → sym (Eval0H (Vec.drop k xs))
   
--  FreeOfVar→ev (P ·X+ Q) zero u = Q ,
--    λ { (x ∷ xs) → RT'.+IdL' _ _ (RT'.0LeftAnnihilates' _ _
--      ((fst (snd (IHR?0 P)) u (x ∷ xs)))) }
--  FreeOfVar→ev {suc n} (P HornerForms.·X+ Q) (suc k) (p , q) =
--    let (P' , p') = FreeOfVar→ev P (suc k) p 
--        (Q' , q') = FreeOfVar→ev Q k q
--    in (P' ·X+ Q') , λ { (x ∷ xs) →
--      cong₂ _+‵_ (cong (_·‵ x) (p' (x ∷ xs))) (q' xs) }


--  HeadVarOnlyInPow : ∀ {n} → IteratedHornerForms (suc n) → ℕ → Type (ℓ-suc ℓ)
--  HeadVarOnlyInPow h zero = FreeOfVar h zero
--  HeadVarOnlyInPow 0H (suc k) = ⊥*
--  HeadVarOnlyInPow (P HornerForms.·X+ Q) (suc k) =
--     HeadVarOnlyInPow P k × [ fst (IHR?0 Q)  ]ᵗʸ

 
 
--  record Elimination {n : ℕ}
--           (P : IteratedHornerForms (suc n))
--           (iX : Fin (suc n)) (k : ℕ₊₁) : Type (ℓ-max ℓ' ℓ) where
--   -- constructor 
--   field   
--    S Q : IteratedHornerForms n
--    S·xᵏ+Q≡P : ∀ xs → 
--        (eval S (drop iX xs) ·‵ (lookup iX xs ^ ℕ₊₁→ℕ k)) +‵ eval Q (drop iX xs)
--           ≡ eval P xs 

--  IsolatedPowerHeadVar : ∀ {n} → IteratedHornerForms (suc n) → ℕ → Type (ℓ-suc ℓ)
--  IsolatedPowerHeadVar 0H _ = ⊥*
--  IsolatedPowerHeadVar (P ·X+ Q) m = HeadVarOnlyInPow P m

--  HeadVarOnlyInPow→ev : ∀ {n} P m → HeadVarOnlyInPow {n} P m →
--     Σ[ P' ∈ IteratedHornerForms n ]
--       (∀ x xs → eval P' xs ·‵ x ^ m ≡ eval P (x ∷ xs) )
--  HeadVarOnlyInPow→ev P zero v =
--    map-snd (λ u x xs → R‵.·IdR _ ∙ sym (u (x ∷ xs))) (FreeOfVar→ev _ _ v)
--  HeadVarOnlyInPow→ev (P ·X+ Q) (suc m) (u , v) =
--    map-snd (λ w x xs →
--         (   cong₂ _·‵_ refl (R‵.·Comm _ _)
--          ∙∙  R‵.·Assoc _ _ _
--          ∙∙ cong (_·‵ x) (w x xs)
--          )
--       ∙ sym (RT'.+IdR' _ _ (fst (snd (IHR?0 Q)) v xs ∙ Eval0H xs)))
--      (HeadVarOnlyInPow→ev P m u)
   
 
--  toElimination : ∀ {n} P m → (IsolatedPowerHeadVar P m) → Elimination {n} P zero (1+ m)
--  toElimination (P ·X+ Q) k hvm =  
--    let (S , eqtion) = HeadVarOnlyInPow→ev P k hvm
--    in record { S = S
--              ; Q = Q
--              ; S·xᵏ+Q≡P = λ { (x ∷ xs) →
--                     cong₂ _+‵_
--                       ( cong₂ _·‵_ refl (R‵.·Comm _ _)
--                           ∙∙  R‵.·Assoc _ _ _
--                           ∙∙ cong (_·‵ x) (eqtion x xs))
--                       refl } }
                   

--  IsolatedPowerVar : ∀ {n} → IteratedHornerForms n → Fin n → ℕ → Type (ℓ-suc ℓ)
--  IsolatedPowerVar {suc n} 0H _ _ = ⊥*
--  IsolatedPowerVar {suc n} (P ·X+ Q) zero m =
--    HeadVarOnlyInPow P m
--  IsolatedPowerVar {suc n} (P ·X+ Q) (suc k) m =
--    IsolatedPowerVar P (suc k) m × IsolatedPowerVar Q k m


--  -- IsolatedPowerVar→ev : ∀ {n} P → ∀ k m →  IsolatedPowerVar {suc n} P k m
--  --    → Elimination P k (1+ m)
--  -- IsolatedPowerVar→ev {n} P@(_ ·X+ _) zero = toElimination P 
--  -- IsolatedPowerVar→ev {suc n} (P ·X+ R) (suc k) m (p , r) =
--  --   let RE = (IsolatedPowerVar→ev {n} R k m r)
--  --       PE = (IsolatedPowerVar→ev {suc n} P (suc k) m p)
--  --   in record { S = PE .S ·X+ RE .S ; Q = PE .Q ·X+ RE .Q ;
--  --        S·xᵏ+Q≡P = λ {(x ∷ xs) b v →
--  --           cong (_+‵ b) (((R‵.·DistL+ _ _ _ ∙ cong₂ _+‵_
--  --             ( sym (R‵.·Assoc _ _ _)
--  --              ∙∙ cong₂ _·‵_ refl (R‵.·Comm _ _) ∙∙ (R‵.·Assoc _ _ _) ) refl)
--  --              ∙ sym (RT'.+IdR' _ _ (R‵.+InvR _)))
--  --             ∙ RT'.+ShufflePairs _ _ _ _)
--  --            ∙ sym (R‵.+Assoc _ _ _) ∙
--  --            cong₂ _+‵_ (sym (R‵.·DistL+ _ _ _)
--  --              ∙ cong (_·‵ x) (PE .a·xᵏ≡p (x ∷ xs) _
--  --              refl))
--  --             ((  sym (R‵.+Assoc _ _ _)
--  --               ∙ cong₂ _+‵_ refl
--  --                 (R‵.+Comm _ _))
--  --              ∙ RE .a·xᵏ≡p xs (b -‵ (eval P (x ∷ xs) ·‵ x))
--  --               (sym (RT'.plusMinus _ _) 
--  --                ∙ cong (_-‵ (eval P (x ∷ xs) ·‵ x)) (R‵.+Comm _ _ ∙ v))) } }   
--  --   where open Elimination

--  CommonDenom : ⟨R⟩ → ⟨R⟩ → Type ℓ
--  CommonDenom a b = 
--              Σ[ (a' , b' , c ) ∈ ⟨R⟩ × ⟨R⟩ × ⟨R⟩ ]
--                 (a ≡ a' · c) × (b ≡ b' · c)
 
--  trivialCD : ∀ a b → CommonDenom a b
--  trivialCD a b = (a , (b , 1r)) , sym (·IdR _) , sym (·IdR _)

--  PoorFactor : ∀ {n} → (P : IteratedHornerForms n) → Type (ℓ-max ℓ ℓ')
                        
--  PoorFactor {n} P = Σ[ a ∈ Maybe ⟨R⟩ ] Σ[ m ∈ Monomial n ]
--                         Σ[ P' ∈ IteratedHornerForms n ]
--                          (∀ xs → just (eval P xs) ≡
--                              (      (map-Maybe (fst hom) a
--                              mb·‵mb (evMonomial m xs))
--                              mb·‵mb (just (eval P' xs))))

--  PolynomialTerm· : ∀ {n} → PolynomialTerm n → PolynomialTerm n → PolynomialTerm n
--  PolynomialTerm· = {!!}
 
--  module _ (commonDenom : ∀ a b → CommonDenom a b) where
--   commonDenomPolynomialTerm : ∀ n → PolynomialTerm n → PolynomialTerm n →
--             {!!}
--   commonDenomPolynomialTerm = {!!}
--   -- poorFactor : ∀ {n} P → PoorFactor {n} P
--   -- poorFactor = {!!}


-- --  Horner→Poly : ∀ {n} → Maybe (Discrete ⟨R⟩) → Maybe ((x : ⟨R⟩) → Maybe (Σ[ -x ∈ ⟨R⟩ ] - -x ≡ x))
-- --                      → (h : IteratedHornerForms n)
-- --                      → Σ (Polynomial n) λ pf → ∀ xs → evPolynomial pf xs ≡ eval h xs 
-- --  Horner→Poly nothing _ (const x) = [ true , (just x) , [] ] , λ {[] → refl}
-- --  Horner→Poly (just _≟_) mbNeg? (const x) =
-- --     hlp (x ≟ 0r) (x ≟ 1r) (Mb.rec nothing (_$ x) mbNeg?) (x ≟ (- 1r))
-- --   where
-- --   hlp : Dec _ →  Dec _ → Maybe _ → Dec _ → _
-- --   hlp (yes x≡0) _ _ _ = [] , λ {[] → sym (IsCommRingHom.pres0 (snd hom)) ∙ cong (hom .fst) (sym x≡0) }
-- --   hlp _ (yes x≡1) _ x₁ =
-- --     [ true , nothing , [] ] , λ {[] → sym (IsCommRingHom.pres1 (snd hom)) ∙ cong (hom .fst) (sym x≡1)}
-- --   hlp _ (no ¬p) _ (yes x≡-1) =
-- --     [ false , nothing , [] ] , λ {[] → sym (IsCommRingHom.pres- (snd hom) 1r
-- --       ∙ cong -‵_ (IsCommRingHom.pres1 (snd hom))) ∙ cong (hom .fst) (sym x≡-1)}
-- --   hlp _ (no ¬p) (just (-x , p)) _ = [ false , (just -x) , [] ] ,
-- --     λ { [] → sym (IsCommRingHom.pres- (snd hom) -x) ∙
-- --             cong (fst hom) p} 
-- --   hlp _ (no ¬p) _ (no ¬p₁) = [ true , (just x) , [] ] , λ {[] → refl}

-- --  Horner→Poly _ _ 0H = [] , λ _ → refl
-- --  Horner→Poly mbD mbN (h₀ ·X+ h₁) =
-- --   let p₀ , q₀ = Horner→Poly mbD mbN h₀
-- --       p₁ , q₁ = Horner→Poly mbD mbN h₁
-- --   in Poly·X p₀ L.++ Poly↑ p₁ , λ { vvs@(v ∷ vs) →
-- --           evPolynomial++ (Poly·X p₀) (Poly↑ p₁) vvs
-- --        ∙ R‵.+Comm _ _ ∙ cong₂ _+‵_
-- --           (evPolynomial·X p₀ v vs ∙ cong (_·‵ v) (q₀ (v ∷ vs)))
-- --           (evPolynomial↑ p₁ v vs ∙ q₁ vs)}


-- --  module Decidable (_≟_ : Discrete ⟨R⟩)
-- --                   (mbNeg? : (x : ⟨R⟩) → Maybe (Σ[ -x ∈ ⟨R⟩ ] - -x ≡ x)) where



-- --   -- poorFactor : ∀ {n} P → PoorFactor {n} P
-- --   -- poorFactor P = {!P!}

  

-- --   HF-Maybe-prfₕ : {n : ℕ} (e₁ e₂ : IteratedHornerForms n) 
-- --                    → Maybe [ fst (IHR? e₁ e₂) ]ᵗʸ
-- --   HF-Maybe-prfₕ e₁ e₂ =
-- --    sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR? e₁ e₂))))


-- --   HF-Maybe-prf : {n : ℕ} (e₁ e₂ : RExpr n) 
-- --                    → Maybe [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ
-- --   HF-Maybe-prf e₁ e₂ = HF-Maybe-prfₕ (normalize e₁) (normalize e₂)

-- --   mbIsConstPossiblyNonNull : {n : ℕ}
-- --         → (e : IteratedHornerForms n)
-- --         → Maybe (IsConstPossiblyNonNull e)
-- --   mbIsConstPossiblyNonNull (const _) = just _
-- --   mbIsConstPossiblyNonNull 0H = nothing
-- --   mbIsConstPossiblyNonNull (P ·X+ Q) =
-- --     ⦇ (sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR?0 P)))))
-- --     , (mbIsConstPossiblyNonNull Q) ⦈

-- --   mbFreeOfVar : ∀ {n} P k → Maybe (FreeOfVar {n} P k)
-- --   mbFreeOfVar 0H k = just _
-- --   mbFreeOfVar (P ·X+ Q) zero =
-- --    sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR?0 P)))) 
-- --   mbFreeOfVar (P ·X+ Q) (suc k) =
-- --     ⦇ (mbFreeOfVar P (suc k)) , (mbFreeOfVar Q k) ⦈
  

-- --   mbHeadVarOnlyInPow : {n : ℕ}
-- --         → (P : IteratedHornerForms (suc n))
-- --         → Maybe (Σ _ (HeadVarOnlyInPow P))
-- --   mbHeadVarOnlyInPow 0H = just (0 , _)
-- --   mbHeadVarOnlyInPow P+Q@(P ·X+ Q) = 
-- --    Mb.rec (do
-- --       v ← sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR?0 Q))))
-- --       (m , u) ← mbHeadVarOnlyInPow P
-- --       pure (suc m , u , v))
-- --      (just ∘ (0 ,_))
-- --      (mbFreeOfVar P+Q zero)


-- --   mbIsolatedPowerVarHead : ∀ {n} P → Maybe (Σ _ (IsolatedPowerHeadVar {n} P))
-- --   mbIsolatedPowerVarHead {n} 0H = nothing
-- --   mbIsolatedPowerVarHead {n} (P HornerForms.·X+ P₁) = mbHeadVarOnlyInPow P

-- --   -- is broken, TODO : fix it
-- --   -- mbIsolatedPowerVar : ∀ {n} P k → Maybe (Σ _ (IsolatedPowerVar {n} P k))
-- --   -- mbIsolatedPowerVar 0H k = nothing
-- --   -- mbIsolatedPowerVar (P ·X+ Q) zero = mbHeadVarOnlyInPow P
-- --   -- mbIsolatedPowerVar (P ·X+ Q) (suc k) = do
-- --   --      (m , u) ← mbIsolatedPowerVar P (suc k)
-- --   --      (m' , u') ← mbIsolatedPowerVar Q k 
-- --   --      decRec
-- --   --        (λ m≡m' →
-- --   --          just (m , u , subst (IsolatedPowerVar Q k) (sym m≡m') u'))
-- --   --         (λ _ → nothing)
-- --   --        (ℕ.discreteℕ m m')
  
-- --   normalizeIHF' : ∀ {n} → (e : IteratedHornerForms n) → ((e ≑ 0ₕ) ⊎ Σ _ (e ≑_ ))
-- --   normalizeIHF'  (const x) =
-- --      decRec (λ x≡0 → inl λ xs i → eval (HornerForms.const (x≡0 i)) xs)
-- --       (λ _ → inr (HornerForms.const x , λ _ → refl)) (x ≟ 0r)
-- --   normalizeIHF' 0H = inl λ _ → refl
-- --   normalizeIHF' e@(e₀ ·X+ e₁) = h (normalizeIHF' e₀) (normalizeIHF' e₁)
-- --     where
-- --     h : ((e₀ ≑ 0ₕ) ⊎ Σ _ (e₀ ≑_ )) → ((e₁ ≑ 0ₕ) ⊎ Σ _ (e₁ ≑_ )) → ((e ≑ 0ₕ) ⊎ Σ _ (e ≑_ ))
-- --     h (inl x₀) (inl x₁) = inl λ { (v ∷ vs) →
-- --        cong₂ R‵._+_
-- --            (RT'.0LeftAnnihilates'  _ _  (x₀ (v ∷ vs)))
-- --            (x₁ vs) ∙ RT'.+IdR' _ _ (Eval0H vs) }
-- --     h x₀ x₁ =
-- --       let (u₀ , y₀) = ⊎.rec (0ₕ ,_) (idfun _) x₀
-- --           (u₁ , y₁) = ⊎.rec (0ₕ ,_) (idfun _) x₁
-- --       in inr (u₀ ·X+ u₁ , λ { (v ∷ vs) i → y₀ (v ∷ vs) i ·‵ v +‵ y₁ vs i })
    

-- --   normalizeIHF : ∀ {n} → (e : IteratedHornerForms n) → Σ _ (e ≑_ )
-- --   normalizeIHF = ⊎.rec (0ₕ ,_) (idfun _) ∘ normalizeIHF'

  
-- --   eval' : {n : ℕ} (P : IteratedHornerForms n)
-- --          → (xs : Vec ⟨R'⟩ n) → Σ ⟨R'⟩ (_≡ eval P xs )
-- --   eval' (const x) xs = _ , refl
-- --   eval' 0H xs = _ , refl
-- --   eval' P@(e₀ ·X+ e₁) vvs@(v ∷ vs) =
-- --     h (normalizeIHF' e₀) (normalizeIHF' e₁)
-- --    where


-- --     ₕ·‵ : Σ ⟨R'⟩ (_≡ fst (eval' e₀ vvs) ·‵ v )
-- --     ₕ·‵ with HF-Maybe-prfₕ e₀ (1ₕ) | HF-Maybe-prfₕ e₀ (-ₕ 1ₕ) 
-- --     ... | nothing | nothing = _ , refl
-- --     ... | just x | _ = v , sym (RT'.·IdL' _ _
-- --        ((snd (eval' e₀ vvs)) ∙∙ (fst (snd (IHR? e₀ (1ₕ))) x vvs) ∙∙
-- --         Eval1ₕ vvs))
-- --     ... | _ | just x = -‵ v , sym (RT'.·IdL' _ _
-- --        (cong -‵_ (((snd (eval' e₀ vvs)) ∙∙ (fst (snd (IHR? e₀ (-ₕ 1ₕ))) x vvs) ∙∙
-- --           (-EvalDist 1ₕ vvs ∙ cong -‵_ (Eval1ₕ vvs))))
-- --         ∙ RT'.-Idempotent _))
-- --      ∙ RT'.-Dist· _ _ 

     


-- --     h : ((e₀ ≑ 0ₕ) ⊎ Σ _ (e₀ ≑_ )) → ((e₁ ≑ 0ₕ) ⊎ Σ _ (e₁ ≑_ )) → Σ ⟨R'⟩ (_≡ eval P vvs )
-- --     h (inl x₀) (inl x₁) =  0r‵ , 
-- --             sym (RT'.0LeftAnnihilates'  _ _  (x₀ vvs))
-- --         ∙ sym (RT'.+IdR' _ _ (x₁ vs ∙ Eval0H vs))
-- --     h x₀@(inr _) (inl x₁) =  _ ,
-- --       snd ₕ·‵ ∙ cong (_·‵ v) (snd (eval' e₀ vvs))
-- --         ∙ sym (RT'.+IdR' _ _ (x₁ vs ∙ Eval0H vs))
-- --     h (inl x₁) (inr x) = _ , snd (eval' e₁ vs) ∙ sym (RT'.+IdL' _ _
-- --        (RT'.0LeftAnnihilates'  _ _  (x₁ vvs)))
-- --     h (inr x₁) (inr x) = _ , cong₂ _+‵_
-- --       (snd ₕ·‵ ∙ cong (_·‵ v) (snd (eval' e₀ vvs)))
-- --       (snd (eval' e₁ vs))


-- --   normalizeByDec :
-- --     {n : ℕ} (e : RExpr n) (xs : Vec (fst R') n) 
-- --     →  Σ _ (⟦ e ⟧ xs ≡_)
-- --   normalizeByDec e xs = evPolynomial
-- --                          (Horner→Poly (just _≟_) (just mbNeg?) (fst (normalizeIHF (normalize e))) .fst) xs ,
-- --         sym (isEqualToNormalform e xs)
-- --      ∙∙ snd (normalizeIHF (normalize e)) xs
-- --      ∙∙ sym ((Horner→Poly (just _≟_) (just mbNeg?) (fst (normalizeIHF (normalize e))) . snd) xs)

-- --   tryElimForHead : {n : ℕ} (e₁ e₂ : RExpr (suc n)) →
-- --     Maybe (Σ _ _)
-- --   tryElimForHead e₁ e₂ = 
-- --      do let (ihf , v) = normalizeIHF (normalize (e₁ +' -' e₂))
-- --         (m , u) ← mbIsolatedPowerVarHead ihf 
-- --         just (1+ m , toElimination ihf m u)


-- --   solveForHead : {n : ℕ} (e₁ e₂ : RExpr (suc n)) (xs : Vec (fst R') (suc n))
-- --     → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs → Maybe (Σ ((fst R') × (fst R')) λ (lhs , rhs) → lhs ≡ rhs)
-- --   solveForHead e₁ e₂ xs e₁≡e₂ = 
-- --      do let (ihf , v) = normalizeIHF (normalize (e₁ +' -' e₂))
-- --         (m , u) ← mbIsolatedPowerVarHead ihf 
-- --         let p = toElimination ihf m u
-- --             (ihfS , eqS) = normalizeIHF (S p)
-- --             (polyS , polyS=) = Horner→Poly (just _≟_) (just mbNeg?) ihfS
-- --             (ihfQ , eqQ) = normalizeIHF (-ₕ (Q p))
-- --             (polyQ , polyQ=) = Horner→Poly (just _≟_) (just mbNeg?) ihfQ
-- --             pp = cong₂ _+‵_ (cong₂ _·‵_ (polyS= (drop zero xs)
-- --                         ∙ sym (eqS (drop zero xs)))
-- --                     (^'≡^ (lookup zero xs) (suc m)))
-- --                    (cong -‵_ (polyQ= (drop zero xs) ∙
-- --                     sym (eqQ (drop zero xs)) ∙ -EvalDist (Q p) _) ∙
-- --                      RT'.-Idempotent _)
-- --                     ∙∙ S·xᵏ+Q≡P p xs  ∙∙
-- --                    sym (v xs) ∙ isEqualToNormalform (e₁ +' -' e₂) xs
-- --                      ∙ RT'.+InvR' _ _ e₁≡e₂
            
-- --         just (_ , (
-- --                   RT'.equalByDifference _ _ pp))
-- --     where open Elimination
    
-- --   -- pickEliminations : {n : ℕ} (e₁ e₂ : RExpr (suc n)) (xs : Vec (fst R') (suc n)) →
-- --   --   Vec (Maybe ℕ) (suc n)
-- --   -- pickEliminations e₁ e₂ xs = 
-- --   --   let (ihf , u) = normalizeIHF (normalize (e₁ +' -' e₂))
-- --   --   in tabulate (λ k →
-- --   --         map-Maybe (fst) (mbIsolatedPowerVar ihf k))


-- --   solveByDifference :  {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
-- --      → fst (eval' (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) xs) ≡ 0r‵
-- --      → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
-- --   solveByDifference e₁ e₂ xs ev=0 =
-- --       RT'.equalByDifference _ _ $ 
-- --          cong₂ _+‵_ (sym (isEqualToNormalform e₁ xs))
-- --           (cong -‵_ (sym (isEqualToNormalform e₂ xs)) ∙ sym (-EvalDist (normalize e₂) xs))
-- --           ∙ sym (+Homeval (normalize e₁) (-ₕ (normalize e₂)) xs) ∙
-- --             snd (normalizeIHF (normalize (e₁ +' -' e₂))) xs ∙
-- --              sym (snd (eval' (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) xs)) ∙ ev=0


-- --   solveByDifference' :  {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
-- --      → evPolynomial (Horner→Poly (just _≟_) (just mbNeg?)
-- --       (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) . fst) xs
-- --        ≡ 0r‵ → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
-- --   solveByDifference' e₁ e₂ xs ev=0 = 
-- --       RT'.equalByDifference _ _ $ 
-- --          cong₂ _+‵_ (sym (isEqualToNormalform e₁ xs))
-- --           (cong -‵_ (sym (isEqualToNormalform e₂ xs)) ∙ sym (-EvalDist (normalize e₂) xs))
-- --           ∙ sym (+Homeval (normalize e₁) (-ₕ (normalize e₂)) xs) ∙
-- --               (snd (normalizeIHF (normalize (e₁ +' -' e₂))) xs)
-- --              ∙ sym ((Horner→Poly (just _≟_) (just mbNeg?)
-- --               (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) . snd) xs) ∙ ev=0



-- -- -- 

-- --  -- congSolve :
-- --  --   {n : ℕ} (e₁ e₂ : RExpr n) → ∀ {xs xs' : Vec (fst R') n} → xs ≡ xs'
-- --  --   → fst (IHR? (normalize e₁) (normalize e₂)) → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs'
-- --  -- congSolve e₁ e₂ {xs} {xs'} p z =
-- --  --   ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
-- --  --   eval (normalize e₁) xs ≡⟨
-- --  --    cong₂ eval (fst (snd (IHR? (normalize e₁) (normalize e₂))) z) p ⟩
-- --  --   eval (normalize e₂) xs' ≡⟨ isEqualToNormalform e₂ xs' ⟩
-- --  --   ⟦ e₂ ⟧ xs' ∎

-- --  -- solveByPath :
-- --  --   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
-- --  --   → eval (normalize e₁) xs ≡ eval (normalize e₂) xs → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
-- --  -- solveByPath e₁ e₂ xs p =
-- --  --    ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
-- --  --    eval (normalize e₁) xs ≡⟨ p ⟩
-- --  --    eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
-- --  --    ⟦ e₂ ⟧ xs ∎
