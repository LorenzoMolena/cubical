module Cubical.Tactics.CommRingSolver.Reflection where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat.Literals

open import Cubical.Data.Int as Slowℤ using (fromNegℤ; fromNatℤ)
open import Cubical.Data.Nat using (ℕ; discreteℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatPlusOne
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Bool
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_)

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing

import Cubical.Algebra.CommRing.Properties as CommRingProperties 
import Cubical.Algebra.Ring.Properties as RingProperties 

open import Cubical.Tactics.CommRingSolver.AlgebraExpression

open import Cubical.Tactics.CommRingSolver.Solver
open import Cubical.Tactics.CommRingSolver.Config
open import Cubical.Tactics.CommRingSolver.GenericCommRing
open import Cubical.Reflection.Sugar
open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Utilities using (quoteDefsfNames;ω[];_ω∷_) public
open import Cubical.Tactics.Reflection.Goals

open import Cubical.Data.Int using (ℤ;pos;negsuc)
import Cubical.Data.Fast.Int as Fastℤ
import Cubical.Data.Fast.Int.Order as ℤ
import Cubical.Algebra.CommRing.Instances.Fast.Int as Fastℤ'

-- import Cubical.Data.Rationals as ℚ
-- import Cubical.Algebra.CommRing.Instances.Rationals as ℚ'
import Cubical.HITs.SetQuotients as SetQuotient

open import Cubical.Data.List.Dependent as DL using (_∷_ ; P[_] ; []) public
import Cubical.Algebra.AbGroup.Base as AbGroup

open import Cubical.Tactics.CommRingSolver.Config

private
 variable
  ℓ' ℓ : Level

module CommRingSolver (crs : CommRingSolverConfig) where

 open CommRingSolverConfig crs

 Fuel = ℕ

 fuelBudget : Fuel
 fuelBudget = 10000000


 module CommRingReflection  where

  open RingReflectionMatcher ringReflectionMatcher

  module _ (basering cring : Term) where
   module _ (matchTerm : (Term → TC (Template × Vars)) → Term → TC (Maybe (Template × Vars))) where

    buildExpression : Fuel → Term → TC (Template × Vars)
    buildExpression (ℕ.zero) t =
      typeError ("OutOfFuel in Cubical.Tactics.CommRingSolver.GenericCommRing" ∷nl [ t ]ₑ)

    buildExpression (ℕ.suc 𝓕) t = do
      (just x) ← matchTerm  (buildExpression 𝓕) t
        where nothing → do
           allowPolyVar ← polyVarGuard t 
           returnTC (if allowPolyVar
            then ((λ ass → polynomialVariable (ass t)) , t ∷ [])
            else  ((λ _ → con (quote K) v[ t ]) , []))
      returnTC x

   toAlgebraExpression' : (Vars → Vars) → Term × Term → TC (Term × Term × Vars)
   toAlgebraExpression' f (lhs , rhs) = do

       matchTerm ← mkMatchTermTC basering cring
       r1 ← buildExpression matchTerm fuelBudget lhs
       r2 ← buildExpression matchTerm fuelBudget rhs
       vars ← returnTC (f (appendWithoutRepetition (snd r1) (snd r2)))
       returnTC (
         let ass : VarAss
             ass n = indexOf n vars
         in (fst r1 ass , fst r2 ass , vars ))

   toAlgebraExpression'2 : (Vars → Vars) → Term × Term → Term × Term → TC
      ((Term × Term) × (Term × Term) × Vars)
   toAlgebraExpression'2 f (lhs , rhs) (lhs' , rhs') = do

       matchTerm ← mkMatchTermTC basering cring
       r1 ← buildExpression matchTerm fuelBudget lhs
       r2 ← buildExpression matchTerm fuelBudget rhs
       r1' ← buildExpression matchTerm fuelBudget lhs'
       r2' ← buildExpression matchTerm fuelBudget rhs'
       vars ← returnTC (f (appendWithoutRepetition (appendWithoutRepetition (snd r1) (snd r2))
            (appendWithoutRepetition (snd r1') (snd r2'))))
       returnTC (
         let ass : VarAss
             ass n = indexOf n vars
         in ((fst r1 ass , fst r2 ass) , (fst r1' ass , fst r2' ass) , vars ))


   toAlgebraExpression : Term × Term → TC (Term × Term × Vars)
   toAlgebraExpression =  toAlgebraExpression' (λ x → x)

   toAlgebraExpressionLHS : Term → TC (Term × Vars)
   toAlgebraExpressionLHS lhs = do

       matchTerm ← mkMatchTermTC basering cring
       
       (r , vars) ← buildExpression matchTerm fuelBudget lhs
       returnTC (
         let ass : VarAss
             ass n = indexOf n vars
         in (r ass , vars ))

-- (quote ETNF.solveByDec)
--      (quote ETNF≟.HF-Maybe-prf

 module _ where


  refineRingGoal : Term → Term → TC Unit
  refineRingGoal expr hole = do
       nForm ← withReduceDefs
         (false , (quote (CommRingProperties.Exponentiation._^_)
                 ∷ quote (RingProperties.RingTheory.fromℕ)
                 ∷ quote AbGroup.IsAbGroup._-_
                 ∷ [ quote CommRingStr._-_ ])) (normalise expr) 
       unify hole nForm


  module _ where
   
   normalizeCallWithVars : ℕ → Vars → Term → Term  → Term
   normalizeCallWithVars n vars CRSC lhs =
       def (quote SansReflection.Decidable.normalizeByDec)
           (CRSC v∷  (ℕAsTerm n) v∷ lhs 
             v∷ (variableList vars)
             ∷ [])

       where
         variableList : Vars → Arg Term
         variableList [] = varg (con (quote emptyVec) [])
         variableList (t ∷ ts)
           = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))




   normalize!-macro : Term → TC Unit
   normalize!-macro hole = withReduceDefs
       (false , doNotUnfold)
     do
       commRing ← quoteTC R`
       baseCommRing ← quoteTC R
       crsTerm ← quoteωTC crs
       goal ← inferType hole >>= normalise


       -- wait-for-type goal
       just (lhs , rhsMeta) ← get-boundaryLHS goal
         where
           nothing
             → typeError(strErr "The CommRingSolver failed to parse the goal "
                                ∷ termErr goal ∷ [])

       (lhs' , vars) ← 
           CommRingReflection.toAlgebraExpressionLHS baseCommRing commRing lhs

       
       (preNForm , solution) ← unquoteSigma (normalizeCallWithVars (length vars) vars crsTerm lhs')

       refineRingGoal preNForm rhsMeta
       unify hole solution


  private
   solverCallWithVars : ℕ → Vars → Term → Term → Term → Maybe Term → Term
   solverCallWithVars n vars CRSC lhs rhs mbPrfTrm =
       def (quote SansReflection.solveByDec) 
           (CRSC v∷ (ℕAsTerm n) v∷ lhs v∷ rhs
             v∷ (variableList vars)
             ∷ fromJust-def
                  (def (quote SansReflection.Decidable.HF-Maybe-prf)
                    (CRSC v∷ (ℕAsTerm (length vars)) v∷ lhs v∷ v[ rhs ]))
                  mbPrfTrm             
              v∷ [])

       where
         variableList : Vars → Arg Term
         variableList [] = varg (con (quote emptyVec) [])
         variableList (t ∷ ts)
           = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))


  solve!-macro : Term → TC Unit
  solve!-macro hole = withReduceDefs
      (false , doNotUnfold)
    do
      commRing ← quoteTC R`
      baseCommRing ← quoteTC R
      crsTerm ← quoteωTC crs
      goal ← inferType hole >>= normalise


      Wait.wait-for-type (λ _ → pure _) goal
      just (lhs , rhs) ← get-boundary goal
        where
          nothing
            → typeError(strErr "The CommRingSolver failed to parse the goal "
                               ∷ termErr goal ∷ [])

      (lhs' , rhs' , vars) ← CommRingReflection.toAlgebraExpression baseCommRing commRing (lhs , rhs)


      let solution = solverCallWithVars (length vars) vars crsTerm lhs' rhs'
      unify hole (solution nothing) 
        <|> do prfHole ← checkType unknown unknown
               unify hole (solution (just prfHole))
               solutionType ← (inferType (solution nothing) >>= normalise)
                   <|> typeError (map,ₑ vars ++ₑ map,ₑ (lhs ∷ rhs ∷ []))
               -- (Mb.rec
               (typeError (("solution type: " ∷nl [ solutionType ]ₑ)
                   ++nl " vars: " ∷nl (map␤ₑ vars
                   ++nl " goalEnds: " ∷nl map,ₑ (lhs' ∷ rhs' ∷ []))))
                 -- (λ _ → do
                 --    lhsMeta ← checkType unknown unknown
                 --    (preNForm , solution) ←
                 --            unquoteSigma (normalizeCallWithVars (length vars) vars crsTerm lhs')

                 --    refineRingGoal preNForm lhsMeta
                 --    typeError [ lhsMeta ]ₑ 
                 --    )
                 --   mbDiscreteScalars)



  module _ where
   private
    solveForCallWithVars : ℕ → Vars → Term → Term → Term → Term → Term
    solveForCallWithVars n vars CRSC lhs rhs eqTerm =
        def (quote SansReflection.Decidable.solveForHead)
            (CRSC v∷ (ℕAsTerm (ℕ.predℕ n)) v∷ lhs v∷ rhs 
              v∷ (variableList vars) ∷ eqTerm
              v∷ [])

        where
          variableList : Vars → Arg Term
          variableList [] = varg (con (quote emptyVec) [])
          variableList (t ∷ ts)
            = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))


   solveFor!-macro : Term → Term → Term → TC Unit
   solveFor!-macro unknVar eqtn hole = withReduceDefs
       (false , doNotUnfold)
     do
       commRing ← quoteTC R`
       baseCommRing ← quoteTC R
       crsTerm ← quoteωTC crs
       providedPathTy ← inferType eqtn >>= normalise
       (lhsGoalHole , _) ← newHole
       (rhsGoalHole , _) ← newHole
       holeTy ← inferType hole
       unify holeTy (def (quote _≡_) (lhsGoalHole v∷ rhsGoalHole v∷ []))
       wait-for-type providedPathTy
       just (lhs , rhs) ← get-boundary providedPathTy
         where
           nothing
             → typeError(strErr "The sovleFor!-macro (ring solver) failed to parse the goal "
                                ∷ termErr providedPathTy ∷ [])

       (lhs' , rhs' , vars) ← 
           CommRingReflection.toAlgebraExpression' baseCommRing commRing
              (prependWithoutRepetition unknVar) (lhs , rhs)

       
       (ends , result) ← unquoteJust (solveForCallWithVars (length vars) vars crsTerm lhs' rhs' eqtn)
                  >>= unquoteSigma
       (lhsRes , rhsRes) ← unquoteSigma ends

       refineRingGoal lhsRes lhsGoalHole
       refineRingGoal rhsRes rhsGoalHole


       unify hole result

 --  module _ (eliminateName : Name) where
   private
    eliminateCallWithVars : ℕ → Vars → Term → Term → Term → Term → Term → Term → Term → Term
    eliminateCallWithVars n vars CRSC lhs rhs lhs' rhs' eqTerm eqTerm' =
        def (quote SansReflection.Decidable.eliminateHead)
            (CRSC v∷ (ℕAsTerm (ℕ.predℕ n)) v∷
               lhs v∷ rhs v∷  lhs' v∷ rhs' v∷
              (variableList vars) ∷ eqTerm v∷ eqTerm' v∷ [])

        where
          variableList : Vars → Arg Term
          variableList [] = varg (con (quote emptyVec) [])
          variableList (t ∷ ts)
            = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))


   eliminate!-macro : Term → Term → Term → Term → Term → TC Unit
   eliminate!-macro unknVar eqtn eqtn' lemmasHole hole = withReduceDefs
       (false , doNotUnfold)
     do
       commRing ← quoteTC R`
       baseCommRing ← quoteTC R
       crsTerm ← quoteωTC crs
       providedPathTy ← inferType eqtn >>= normalise
       providedPathTy' ← inferType eqtn' >>= normalise
              
       holeTy ← inferType hole
       wait-for-type providedPathTy
       wait-for-type providedPathTy'
       just (lhs , rhs) ← get-boundary providedPathTy
         where
           nothing
             → typeError(strErr "The sovleFor!-macro (ring solver) failed to parse the goal "
                                ∷ termErr providedPathTy ∷ [])
       just (lhs' , rhs') ← get-boundary providedPathTy'
         where
           nothing
             → typeError(strErr "The sovleFor!-macro (ring solver) failed to parse the goal "
                                ∷ termErr providedPathTy' ∷ [])

       ((lhs* , rhs*) , (lhs'* , rhs'*) , vars) ← 
           CommRingReflection.toAlgebraExpression'2 baseCommRing commRing
              (prependWithoutRepetition unknVar) (lhs , rhs) (lhs' , rhs')

       unquoteSum (eliminateCallWithVars (length vars) vars crsTerm
              
             lhs* rhs* lhs'* rhs'* eqtn eqtn')
                  >>= λ where
          (inr r) → do
            (u , solutionNotYetAppliedToLemmas) ← unquoteSigma r
            (_ , lhsRes) ← unquoteSigma u
            (lhsGoalHole , _) ← newHole
            unify holeTy (def (quote _≡_) (lhsGoalHole v∷ unknown v∷ []))
            refineRingGoal lhsRes lhsGoalHole
            let solution = def (quote _$_) (solutionNotYetAppliedToLemmas v∷ v[ lemmasHole ]) 
            -- inferType result >>= normalise >>= λ nty →  typeError [ nty ]ₑ
            
            unify hole solution
            refineListPHole lemmasHole
            -- typeError [ "test0" ]ₑ
            -- unify lemmas lemmas'
          (inl err) → typeError [ err ]ₑ


  solve!-lemma-macro : Term → Term → TC Unit
  solve!-lemma-macro lemmas hole = withReduceDefs
      (false , doNotUnfold)
    do
      commRing ← quoteTC R`
      baseCommRing ← quoteTC R
      crsTerm ← quoteωTC crs
      goal ← inferType hole >>= normalise


      wait-for-type goal
      just (lhs , rhs) ← get-boundary goal
        where
          nothing
            → typeError(strErr "The CommRingSolver failed to parse the goal "
                               ∷ termErr goal ∷ [])

      (lhs' , rhs' , vars) ← CommRingReflection.toAlgebraExpression baseCommRing commRing (lhs , rhs)
      (missingEqs , _) ← newHole
      let solution = solverCallWithVars (length vars) vars crsTerm lhs' rhs'
                      (just (con (quote just) v[ missingEqs ]))

      unify hole solution
      lemmas' ← satisfySomeTC
        scalarSolver missingEqs
      unify lemmas lemmas'


 -- module _ (solveByDifference-name : Name) where

 --  private
 --   solverCallWithVars : ℕ → Vars → Term → Term → Term → Term → Term
 --   solverCallWithVars n vars R lhs rhs lemmaHole =
 --       def solveByDifference-name
 --           (R v∷ (harg {quantity-ω} (ℕAsTerm n)) ∷ lhs v∷ rhs
 --             v∷ (variableList vars)
 --             ∷ lemmaHole             
 --              v∷ [])

 --       where
 --         variableList : Vars → Arg Term
 --         variableList [] = varg (con (quote emptyVec) [])
 --         variableList (t ∷ ts)
 --           = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))

  

 --  solve_[_]!-macro : Term → Term → TC Unit
 --  solve_[_]!-macro lemma hole = withReduceDefs
 --      (false , doNotUnfold)
 --    do
 --      commRing ← quoteTC ring
 --      baseCommRing ← quoteTC basering
 --      goal ← inferType hole >>= normalise


 --      wait-for-type goal
 --      just (lhs , rhs) ← get-boundary goal
 --        where
 --          nothing
 --            → typeError(strErr "The CommRingSolver failed to parse the goal "
 --                               ∷ termErr goal ∷ [])

 --      (lhs' , rhs' , vars) ← CommRingReflection.toAlgebraExpression baseCommRing commRing (lhs , rhs)

 --      let solution = solverCallWithVars (length vars) vars commRing lhs' rhs' lemma
 --      unify hole solution



 macro
   solve! : Term → TC Unit
   solve! = solve!-macro

   normalize! : Term → TC Unit
   normalize! = normalize!-macro
                   
   
--    -- ring[_][_]! : Term → Term → TC Unit
--    -- ring[_][_]! = GenericCommRingSolverOverInt.solve_[_]!-macro (quote (ETNF≟.solveByDifference'))

   solveFor! : Term → Term → Term → TC Unit
   solveFor! = solveFor!-macro

   eliminate! : Term → Term → Term → Term → Term → TC Unit
   eliminate! = eliminate!-macro


 -- module WithScalarSolver (vars : List ⟨ R` ⟩) where
 --  macro
   -- ring! : Term → Term → TC _
   -- ring! lemma hole =
   --  do varsTms ← traverseList quoteTC vars
   --     solve!-lemma-macro 
   --        scalarSolver
   --        vars lemma hole


mbNegℤ : (x : Fastℤ.ℤ) → Maybe (Σ Fastℤ.ℤ (λ -x → Fastℤ.- -x ≡ x))
mbNegℤ (Fastℤ.pos n) = nothing
mbNegℤ (Fastℤ.negsuc n) = just (Fastℤ.pos (ℕ.suc n) ,  refl)

cdℤ : (a b : Fastℤ.ℤ) → Σ[ (a' , b' , c ) ∈ _ × _ × _ ]
                (a ≡ a' Fastℤ.· c) × (b ≡ b' Fastℤ.· c)
cdℤ a b = _ , snd (Fastℤ.gcdℤ a b)

·lCancelℤ : ∀ c m n → c Fastℤ.· m ≡ c Fastℤ.· n → ¬ c ≡ 0 → m ≡ n
·lCancelℤ = Fastℤ.·lCancel

module SolveOverℤ {ℓ} (cring : CommRing ℓ) where

 module PreSolvers mb·`lCancel mbNotZeroRing mb≢0r→≢0r` where
  config : CommRingSolverConfig
  config .CommRingSolverConfig.ℓ = _
  config .CommRingSolverConfig.ℓ` = _
  config .CommRingSolverConfig.R = Fastℤ'.ℤCommRing
  config .CommRingSolverConfig.commAlg = cring , _ , Fastℤ'.CanonicalHomFromℤ.isHomFromℤ _
  config .CommRingSolverConfig.mbDiscreteScalars = just Fastℤ.discreteℤ
  config .CommRingSolverConfig.mbNeg?Scalar = just mbNegℤ
  config .CommRingSolverConfig.mbCommonDenom = just cdℤ
  config .CommRingSolverConfig.mb·`lCancel = mb·`lCancel
  config .CommRingSolverConfig.mbNotZeroRing = mbNotZeroRing
  config .CommRingSolverConfig.mb≢0r→≢0r` = mb≢0r→≢0r`
  config .CommRingSolverConfig.ringReflectionMatcher =
    GenericCommRingReflection.genericCommRingMatchTerm
  config .CommRingSolverConfig.doNotUnfold = []
  config .CommRingSolverConfig.polyVarGuard = (λ _ → pure true)
  config .CommRingSolverConfig.scalarSolver = (λ _ _ → pure false)

  open CommRingSolver config hiding (solve!-lemma-macro) public

  -- open CommRingSolver.WithScalarSolver overItself

  module OverItself (varsTerms : List Term) where
   overItself : CommRingSolverConfig
   overItself .CommRingSolverConfig.ℓ = _
   overItself .CommRingSolverConfig.ℓ` = _
   overItself .CommRingSolverConfig.R = cring
   overItself .CommRingSolverConfig.commAlg = cring , idCommRingHom _
   overItself .CommRingSolverConfig.mbDiscreteScalars = nothing
   overItself .CommRingSolverConfig.mbNeg?Scalar = nothing
   overItself .CommRingSolverConfig.mbCommonDenom = nothing
   overItself .CommRingSolverConfig.mb·`lCancel = nothing
   overItself .CommRingSolverConfig.mbNotZeroRing = nothing
   overItself .CommRingSolverConfig.mb≢0r→≢0r` = nothing
   overItself .CommRingSolverConfig.ringReflectionMatcher =
     GenericCommRingReflection.genericCommRingMatchTerm
   overItself .CommRingSolverConfig.doNotUnfold = []
   overItself .CommRingSolverConfig.polyVarGuard = (λ tm → pure (elemVars tm varsTerms))
   overItself .CommRingSolverConfig.scalarSolver hole _ = 
    sucesfullM? (solve!-macro hole)

   open CommRingSolver overItself using (solve!-lemma-macro) public

  module _ (vars : List ⟨ cring ⟩ ) where
   macro
    ring! : Term → Term → TC Unit
    ring! lemma hole = do
         varsTms ← traverseList quoteTC vars
         OverItself.solve!-lemma-macro varsTms lemma hole
  
 module Generic = PreSolvers nothing nothing nothing

 module Reasonable ((·`lCancel , notZeroRing , ≢0r→≢0r`) : _ × _ × _)  where
  open PreSolvers (just ·`lCancel) (just notZeroRing) (just ≢0r→≢0r`) public


open SolveOverℤ.Generic using (solve!) public  

open GenericCommRingReflection using (RingNames) public
open RingNames public 

module Discrete {ℓ} (cring : CommRing ℓ)
                    (discreteR : _)
                    (notZeroRing : _)
                    (mbNeg?Scalar : _)
                    (mbCommonDenom : _)
                    (mb·`lCancel : _)
                    (dnfs : _)
                    (matcher : _) where

 config : CommRingSolverConfig
 config .CommRingSolverConfig.ℓ = _
 config .CommRingSolverConfig.ℓ` = _
 config .CommRingSolverConfig.R = cring
 config .CommRingSolverConfig.commAlg = _ , idCommRingHom _
 config .CommRingSolverConfig.mbDiscreteScalars = just discreteR
 config .CommRingSolverConfig.mbNeg?Scalar = mbNeg?Scalar
 config .CommRingSolverConfig.mbCommonDenom = mbCommonDenom
 config .CommRingSolverConfig.mb·`lCancel = mb·`lCancel
 config .CommRingSolverConfig.mbNotZeroRing = just notZeroRing
 config .CommRingSolverConfig.mb≢0r→≢0r` = just λ _ z → z
 config .CommRingSolverConfig.ringReflectionMatcher = matcher
 config .CommRingSolverConfig.doNotUnfold = dnfs
 config .CommRingSolverConfig.polyVarGuard = (λ _ → pure true)
 config .CommRingSolverConfig.scalarSolver = (λ _ _ → pure false)
 
 open CommRingSolver config hiding (solve!-lemma-macro) public

module FastℤRingSolver where
 open Fastℤ hiding (_+'_)
 open Fastℤ'

 FastℤMatcher : RingReflectionMatcher
 FastℤMatcher .RingReflectionMatcher.mkMatchTermTC _ _ = returnTC matchTerm

  where

  scalarℕ : ℕ → TC (Template × Vars)
  scalarℕ n = returnTC (((λ _ →
    con (quote K) (con (quote ℤ.pos) (lit (nat n) v∷ []) v∷ [])) , []))

  module _ (be : (Term → TC (Template × Vars))) where
   open BE q[ ℤCommRing ] be



   buildExpressionFromNat : Term → TC (Template × Vars)
   buildExpressionFromNat (lit (nat x)) = scalarℕ x
   buildExpressionFromNat (con (quote ℕ.zero) []) = `0` []
   buildExpressionFromNat (con (quote ℕ.suc) (con (quote ℕ.zero) [] v∷ [] )) = `1` []
   buildExpressionFromNat (con (quote ℕ.suc) (x v∷ [] )) = do
     r1 ← `1` []
     r2 ← buildExpressionFromNat x
     returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat (def (quote ℕ._+_) (x v∷ y v∷ [])) = do
     r1 ← buildExpressionFromNat x
     r2 ← buildExpressionFromNat y
     returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat (def (quote ℕ._·_) (x v∷ y v∷ [])) = do
     r1 ← buildExpressionFromNat x
     r2 ← buildExpressionFromNat y
     returnTC ((λ ass → con (quote _·'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat (def (quote _ℕ-_) (x v∷ (con (quote ℕ.suc) (y v∷ [] )) v∷ [])) = do
     r1 ← buildExpressionFromNat x
     r2 ← do y' ← do u1 ← `1` []
                     u2 ← buildExpressionFromNat y
                     returnTC {A = Template × Vars} ((λ ass → con (quote _+'_)
                      (fst u1 ass v∷ fst u2 ass v∷ [])) ,
                          appendWithoutRepetition (snd u1) (snd u2))
             returnTC {A = Template × Vars} ((λ ass → con (quote -'_) (fst y' ass v∷ [])) , snd y')
     returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat t' =
    let t = (con (quote ℤ.pos) (t' v∷ []))
    in (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))



   matchTerm : Term → TC (Maybe (Template × Vars))

   matchTerm t@(con (quote ℤ.pos) (x v∷ [])) = do
    just <$> buildExpressionFromNat x
   matchTerm t@(con (quote ℤ.negsuc) (x v∷ [])) =
    do y ← do r1 ← `1` []
              r2 ← buildExpressionFromNat x
              returnTC {A = Template × Vars} ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
                   appendWithoutRepetition (snd r1) (snd r2))
       just <$> returnTC ((λ ass → con (quote -'_) (fst y ass v∷ [])) , snd y)

   matchTerm t@(def (quote -_) xs) = just <$> `-_` xs
   matchTerm t@(def (quote _+_) xs) = just <$> `_+_` xs
   matchTerm t@(def (quote _·_) xs) = just <$> `_·_` xs

   matchTerm _ = returnTC nothing



 config : CommRingSolverConfig
 config .CommRingSolverConfig.ℓ = _
 config .CommRingSolverConfig.ℓ` = _
 config .CommRingSolverConfig.R = Fastℤ'.ℤCommRing
 config .CommRingSolverConfig.commAlg =
  Fastℤ'.ℤCommRing , idCommRingHom _
 config .CommRingSolverConfig.mbDiscreteScalars = just Fastℤ.discreteℤ
 config .CommRingSolverConfig.mbNeg?Scalar = just mbNegℤ
 config .CommRingSolverConfig.mbCommonDenom = just cdℤ
 config .CommRingSolverConfig.mb·`lCancel = just ·lCancelℤ
 config .CommRingSolverConfig.mbNotZeroRing = just (Slowℤ.0≢1-ℤ ∘S sym)
 config .CommRingSolverConfig.mb≢0r→≢0r` = just λ _ z → z
 config .CommRingSolverConfig.ringReflectionMatcher = FastℤMatcher
 config .CommRingSolverConfig.doNotUnfold =
  quoteDefsfNames (ℕ._·_ ω∷ ℕ._+_ ω∷ _+_ ω∷ (-_) ω∷ _·_ ω∷ _ℕ-_ ω∷ ω[])
 config .CommRingSolverConfig.polyVarGuard = (λ _ → pure true)
 config .CommRingSolverConfig.scalarSolver = (λ _ _ → pure false)

 open CommRingSolver config hiding (solve!-lemma-macro) public

open FastℤRingSolver using () renaming (solve! to ℤ!) public

module FastℤPlusRingSolver where
 open Fastℤ hiding (_+'_)
 open Fastℤ'

 FastℤPlusMatcher : RingReflectionMatcher
 FastℤPlusMatcher .RingReflectionMatcher.mkMatchTermTC _ _ = returnTC matchTerm

  where

  scalarℕ : ℕ → TC (Template × Vars)
  scalarℕ n = returnTC (((λ _ →
    con (quote K) (con (quote ℤ.pos) (lit (nat n) v∷ []) v∷ [])) , []))

  module _ (be : (Term → TC (Template × Vars))) where
   open BE q[ ℤCommRing ] be

   Fuel = ℕ

   buildExpression : Fuel → Term → TC (Template × Vars)

   natPlusVariable : Term → TC (Template × Vars)
   natPlusVariable t' =
    let t = (con (quote ℤ.pos) (con (quote ℕ.suc) ((def (quote ℕ₊₁.n) (t' v∷ [])) v∷ []) v∷ []))
    in (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))

     -- do let t = (con (quote ℤ.pos) ((def (quote ℕ₊₁.n) (t' v∷ [])) v∷ []))
     --    debugPrint "intSolver" 20  (strErr "fromNatPlusFallback :" ∷ termErr t ∷ [])
     --    r1 ← scalarℕ 1 -- `1` []
     --    returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ polynomialVariable (ass t) v∷ [])) ,
     --             appendWithoutRepetition (snd r1) (t ∷ []))

   buildExpressionFromNat : Fuel → Term → TC (Template × Vars)
   buildExpressionFromNatPlus : Fuel → Term → TC (Template × Vars)
   buildExpressionFromNatPlus  ℕ.zero _ = typeError [ strErr "outOfFuel" ]
   buildExpressionFromNatPlus f (def (quote _·₊₁_) (x v∷ y v∷ [])) =
    do debugPrint "intSolverVars" 20  (strErr "fromNatPlus t3:" ∷nl x ∷nl y ∷ₑ [])
       r1 ← buildExpressionFromNatPlus f x
       r2 ← buildExpressionFromNatPlus f y
       returnTC ((λ ass → con (quote _·'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
                appendWithoutRepetition (snd r1) (snd r2))



   buildExpressionFromNatPlus f (x@(var _ [])) = natPlusVariable x
    -- buildExpressionFromNat f (con (quote ℕ.suc) (def (quote ℕ₊₁.n) (x v∷ []) v∷ [] ))
     -- do
     --    r1 ← `1` []
     --    let t = (def (quote ℕ₊₁.n) (x v∷ []) )
     --    r2 ← (returnTC {A = (Template × Vars)} ((λ ass → polynomialVariable (ass t)) , t ∷ []))
     --    returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
     --             appendWithoutRepetition (snd r1) (snd r2))

    -- let t = (con (quote ℤ.pos) (t' v∷ []))
    -- in (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))
    -- -- buildExpressionFromNat f (con (quote ℕ.suc) (def (quote ℕ₊₁.n) (x v∷ []) v∷ [] ))

   buildExpressionFromNatPlus f t@(con (quote 1+_) (x@(var _ []) v∷ [])) =
     natPlusVariable t
    -- buildExpressionFromNat f (con (quote ℕ.suc) (x v∷ [] ))


   -- buildExpressionFromNatPlus (ℕ.suc f) (con (quote 1+_)
   --    ((def (quote ℕ._+_) (𝒏@(def (quote ℕ₊₁.n) (n v∷ [])) v∷
   --     (def (quote ℕ._·_) ((def (quote ℕ₊₁.n) (m v∷ [])) v∷ (con (quote ℕ.suc) (𝒏* v∷ [] )) v∷ [])) v∷ [])) v∷ [])) = do
   --   unify 𝒏 𝒏*
   --   buildExpressionFromNatPlus f (def (quote _·₊₁_) (m v∷ n v∷ []))


   -- buildExpressionFromNatPlus (ℕ.suc f) (con (quote 1+_)
   --    ((def (quote ℕ._+_) (n v∷
   --     (def (quote ℕ._·_) (m v∷ (con (quote ℕ.suc) (n* v∷ [] )) v∷ [])) v∷ [])) v∷ [])) = do
   --   unify n n*
   --   buildExpressionFromNatPlus f (def (quote _·₊₁_)
   --    (con (quote 1+_) (m v∷ []) v∷
   --     con (quote 1+_) (n v∷ []) v∷
   --     []))


   buildExpressionFromNatPlus f (con (quote 1+_) ((con (quote ℕ.zero) []) v∷ [])) =
     scalarℕ 1 -- `1` []
   buildExpressionFromNatPlus (ℕ.suc f) (con (quote 1+_) ((con (quote ℕ.suc) (x v∷ [])) v∷ [])) =
    do r1 ← scalarℕ 1 -- `1` []
       r2 ← buildExpressionFromNatPlus f (con (quote 1+_) (x v∷ []))
       returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
                appendWithoutRepetition (snd r1) (snd r2))

   buildExpressionFromNatPlus f (con (quote 1+_) ((lit (nat x)) v∷ [])) = scalarℕ (ℕ.suc x)

   buildExpressionFromNatPlus f (con (quote 1+_) ((def (quote ℕ₊₁.n) (x v∷ []) ) v∷ [])) =
    do  debugPrint "intSolverVars" 20  (strErr "fromNatPlus t1:" ∷ termErr x ∷ [])
        buildExpressionFromNatPlus f x

   buildExpressionFromNatPlus (ℕ.suc f) (def (quote ℤ.0<→ℕ₊₁-fst) (x v∷ [])) =
      buildExpression f x
   buildExpressionFromNatPlus (ℕ.suc f) (con (quote 1+_)
      ((def (quote ℕ._+_) (n v∷
       (def (quote ℕ._·_) (m v∷ sn v∷ [])) v∷ [])) v∷ [])) = do
     unify (con (quote ℕ.suc) (n v∷ [] )) sn
     debugPrint "intSolverVars" 20  (strErr "fromNatPlus t2:" ∷nl termErr n ∷nl termErr m ∷  [])

     buildExpressionFromNatPlus f (def (quote _·₊₁_)
      (con (quote 1+_) (m v∷ []) v∷
       con (quote 1+_) (n v∷ []) v∷
       []))


 -- (def (quote ℕ₊₁.n) (n v∷ []))



   buildExpressionFromNatPlus f t' = natPlusVariable t'

    --    -- buildExpressionFromNat f (con (quote ℕ.suc) (def (quote ℕ₊₁.n) (x v∷ []) v∷ [] ))
    -- typeError (strErr "unexpected in buildExpressionFromNatPlus: \n " ∷ termErr t ∷ [])

 -- (.fst (ℤ.0<→ℕ₊₁ (pos (suc k) ℤ.· pos (suc k₁)) tt))


   buildExpressionFromNat f t@(lit (nat x)) = -- typeError (strErr "scalar: " ∷ termErr t ∷ [])
     scalarℕ x --buildExpressionFromNatLit x
   buildExpressionFromNat f (con (quote ℕ.zero) []) = scalarℕ 0 -- `0` []
   buildExpressionFromNat f (con (quote ℕ.suc) (con (quote ℕ.zero) [] v∷ [] )) = scalarℕ 1 -- `1` []
   buildExpressionFromNat f (con (quote ℕ.suc) ((def (quote ℕ₊₁.n) (n v∷ [])) v∷ [] ))
    = buildExpressionFromNatPlus f n
   buildExpressionFromNat f (con (quote ℕ.suc) (x v∷ [] )) =
     do
     debugPrint "intSolver" 20  (strErr "fromNat suc:" ∷ termErr x ∷ [])
     r1 ← scalarℕ 1 -- `1` []
     r2 ← buildExpressionFromNat f x
     returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat f (def (quote ℕ._+_) (x v∷ y v∷ [])) =
     do
     debugPrint "intSolver" 20  (strErr "buildNateExpr ℕ._+_ :" ∷ termErr x ∷ [])
     r1 ← buildExpressionFromNat f x
     r2 ← buildExpressionFromNat f y
     returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat f (def (quote ℕ._·_) (x v∷ y v∷ [])) =
     do
     r1 ← buildExpressionFromNat f x
     r2 ← buildExpressionFromNat f y
     returnTC ((λ ass → con (quote _·'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat f (def (quote _ℕ-_) (x v∷ (con (quote ℕ.suc) (y v∷ [] )) v∷ [])) =
     do
     r1 ← buildExpressionFromNat f x
     r2 ← do y' ← do u1 ← scalarℕ 1 -- `1` []
                     u2 ← buildExpressionFromNat f y
                     returnTC {A = Template × Vars} ((λ ass → con (quote _+'_) (fst u1 ass v∷ fst u2 ass v∷ [])) ,
                          appendWithoutRepetition (snd u1) (snd u2))
             returnTC {A = Template × Vars} ((λ ass → con (quote -'_) (fst y' ass v∷ [])) , snd y')
     returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat (ℕ.suc f) (def (quote ℕ₊₁→ℕ) (x v∷ [])) =
    buildExpressionFromNatPlus f x
   buildExpressionFromNat f t' =
    let t = (con (quote ℤ.pos) (t' v∷ []))
    in (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))


   buildExpression ℕ.zero _ = typeError [ strErr "outOfFuel" ]
   buildExpression f (def (quote ℕ₊₁→ℤ) (x v∷ [])) =
    buildExpressionFromNatPlus f x

   buildExpression f v@(var _ _) =
     returnTC ((λ ass → polynomialVariable (ass v)) ,
              v ∷ [])



   buildExpression f (def (quote _+_) xs) = `_+_` xs
   buildExpression f (def (quote _·_) xs) = `_·_` xs
   buildExpression f (def (quote -_) xs) = `-_` xs

   buildExpression f t@(def _ xs) =
        (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))

   buildExpression f t@(con (quote pos) (x v∷ [])) = do
     debugPrint "intSolver" 20  (strErr "buildExpr pos:" ∷ termErr x ∷ [])
     buildExpressionFromNat f x
   buildExpression f t@(con (quote negsuc) ((def (quote ℕ₊₁.n) (x v∷ []) ) v∷ [])) =
     do y ← buildExpressionFromNatPlus f x
        returnTC ((λ ass → con (quote -'_) (fst y ass v∷ [])) , snd y)
   buildExpression f t@(con (quote negsuc) (x v∷ [])) =
    do debugPrint "intSolver" 20  (strErr "buildExpr negsuc:" ∷ termErr x ∷ [])
       y ← do r1 ← scalarℕ 1 -- `1` []
              r2 ← buildExpressionFromNat f x
              returnTC {A = Template × Vars} ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
                    appendWithoutRepetition (snd r1) (snd r2))
       returnTC ((λ ass → con (quote -'_) (fst y ass v∷ [])) , snd y)

   buildExpression f t = errorOut' t
   -- there should be cases for variables which are functions, those should be detectable by having visible args
   -- there should be cases for definitions (with arguments)


   matchTerm : Term → TC (Maybe (Template × Vars))
   matchTerm tm = just <$> buildExpression 10000 tm 
   -- matchTerm t@(con (quote pos) (x v∷ [])) = do
   --  just <$> buildExpressionFromNat x
   -- matchTerm t@(con (quote negsuc) (x v∷ [])) =
   --  do y ← do r1 ← `1` []
   --            r2 ← buildExpressionFromNat x
   --            returnTC {A = Template × Vars} ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
   --                 appendWithoutRepetition (snd r1) (snd r2))
   --     just <$> returnTC ((λ ass → con (quote -'_) (fst y ass v∷ [])) , snd y)

   -- matchTerm t@(def (quote -_) xs) = just <$> `-_` xs
   -- matchTerm t@(def (quote _+_) xs) = just <$> `_+_` xs
   -- matchTerm t@(def (quote _·_) xs) = just <$> `_·_` xs

   -- matchTerm _ = returnTC nothing



 config : CommRingSolverConfig
 config .CommRingSolverConfig.ℓ = _
 config .CommRingSolverConfig.ℓ` = _
 config .CommRingSolverConfig.R = Fastℤ'.ℤCommRing
 config .CommRingSolverConfig.commAlg =
  Fastℤ'.ℤCommRing , idCommRingHom _
 config .CommRingSolverConfig.mbDiscreteScalars = just Fastℤ.discreteℤ
 config .CommRingSolverConfig.mbNeg?Scalar = just mbNegℤ
 config .CommRingSolverConfig.mbCommonDenom = just cdℤ
 config .CommRingSolverConfig.mb·`lCancel = just ·lCancelℤ
 config .CommRingSolverConfig.mbNotZeroRing = just (Slowℤ.0≢1-ℤ ∘S sym)
 config .CommRingSolverConfig.mb≢0r→≢0r` = just λ _ z → z
 config .CommRingSolverConfig.ringReflectionMatcher = FastℤPlusMatcher
 config .CommRingSolverConfig.doNotUnfold =
  quoteDefsfNames (ℕ._·_ ω∷ ℕ._+_ ω∷ _+_ ω∷ (-_) ω∷ _·_ ω∷ _ℕ-_ ω∷ _+₁_ ω∷ _·₊₁_ -- ω∷ ℕ₊₁→ℕ -- ω∷ ℕ₊₁→ℤ
    ω∷ ℤ.0<→ℕ₊₁-fst ω∷ ω[])

 config .CommRingSolverConfig.polyVarGuard = (λ _ → pure true)
 config .CommRingSolverConfig.scalarSolver = (λ _ _ → pure false)

 open CommRingSolver config hiding (solve!-lemma-macro) public


--  private
--   module ETNF =  EqualityToNormalform Fastℤ'.ℤCommRing ring
--                   (_ , Fastℤ'.CanonicalHomFromℤ.isHomFromℤ ring)
--   module ETNF≟ = ETNF.Decidable Fastℤ.discreteℤ mbNegℤ (just cdℤ) (just ·lCancelℤ) nothing
--                   nothing nothing

--  module GenericCommRingSolverOverInt =
--    CommRingSolver Fastℤ'.ℤCommRing ring nothing
--     (GenericCommRingReflection.genericCommRingMatchTerm) []
--      (quote ETNF.solveByDec)
--      (quote ETNF≟.HF-Maybe-prf)
--      (λ _ → pure true)

--    -- eliminate! : Term → Term → Term → Term → Term → TC Unit
--    -- eliminate! = GenericCommRingSolverOverInt.eliminate!-macro (quote (ETNF≟.eliminateHead))

-- -- module CommRingSolverMacrosIntDom (ring : CommRing ℓ)
-- --                                   (intDom : ((c m n : ring .fst) →
-- --                                   (snd ring CommRingStr.· c) m ≡ (snd ring CommRingStr.· c) n →
-- --                                   (c ≡ CommRingStr.0r (snd ring) → ⊥) → m ≡ n)) where

-- --  private
-- --   module ETNF =  EqualityToNormalform Fastℤ'.ℤCommRing ring
-- --                   (_ , Fastℤ'.CanonicalHomFromℤ.isHomFromℤ ring)
-- --   module ETNF≟ = ETNF.Decidable Fastℤ.discreteℤ mbNegℤ (just cdℤ) (just ·lCancelℤ) (just intDom)
-- --                     nothing nothing

-- --  module GenericCommRingSolverOverInt =
-- --    CommRingSolver Fastℤ'.ℤCommRing ring (just intDom)
-- --     (GenericCommRingReflection.genericCommRingMatchTerm) []
-- --      (quote ETNF.solveByDec)
-- --      (quote ETNF≟.HF-Maybe-prf)
-- --      (λ _ → pure true)

-- --  macro
-- --    solve! : Term → TC Unit
-- --    solve! = GenericCommRingSolverOverInt.solve!-macro 

-- --    normalize! : Term → TC Unit
-- --    normalize! = GenericCommRingSolverOverInt.normalize!-macro
-- --                    (quote (ETNF≟.normalizeByDec))
   
-- --    ring[_][_]! : Term → Term → TC Unit
-- --    ring[_][_]! = GenericCommRingSolverOverInt.solve_[_]!-macro (quote (ETNF≟.solveByDifference'))

-- --    solveFor! : Term → Term → Term → TC Unit
-- --    solveFor! = GenericCommRingSolverOverInt.solveFor!-macro (quote (ETNF≟.solveForHead))

-- --    eliminate! : Term → Term → Term → Term → Term → TC Unit
-- --    eliminate! = GenericCommRingSolverOverInt.eliminate!-macro (quote (ETNF≟.eliminateHead))


-- -- module _ (ring : CommRing ℓ)

-- --        where

-- --  private
-- --   module ETNF =  EqualityToNormalform ring ring
-- --                   (idCommRingHom _)


-- --   scalarSolver : Term → Term → TC Bool
-- --   scalarSolver hole _ = 
-- --     sucesfullM? (CommRingSolverMacros.GenericCommRingSolverOverInt.solve!-macro ring hole)
    


-- -- module FastℤRingSolver where
-- --  open Fastℤ hiding (_+'_)
-- --  open Fastℤ'

-- --  fastℤMatcher : RingReflectionMatcher
-- --  fastℤMatcher .RingReflectionMatcher.mkMatchTermTC _ _ = returnTC matchTerm

-- --   where

-- --   scalarℕ : ℕ → TC (Template × Vars)
-- --   scalarℕ n = returnTC (((λ _ →
-- --     con (quote K) (con (quote pos) (lit (nat n) v∷ []) v∷ [])) , []))

-- --   module _ (be : (Term → TC (Template × Vars))) where
-- --    open BE q[ ℤCommRing ] be



-- --    buildExpressionFromNat : Term → TC (Template × Vars)
-- --    buildExpressionFromNat (lit (nat x)) = scalarℕ x
-- --    buildExpressionFromNat (con (quote ℕ.zero) []) = `0` []
-- --    buildExpressionFromNat (con (quote ℕ.suc) (con (quote ℕ.zero) [] v∷ [] )) = `1` []
-- --    buildExpressionFromNat (con (quote ℕ.suc) (x v∷ [] )) = do
-- --      r1 ← `1` []
-- --      r2 ← buildExpressionFromNat x
-- --      returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
-- --               appendWithoutRepetition (snd r1) (snd r2))
-- --    buildExpressionFromNat (def (quote ℕ._+_) (x v∷ y v∷ [])) = do
-- --      r1 ← buildExpressionFromNat x
-- --      r2 ← buildExpressionFromNat y
-- --      returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
-- --               appendWithoutRepetition (snd r1) (snd r2))
-- --    buildExpressionFromNat (def (quote ℕ._·_) (x v∷ y v∷ [])) = do
-- --      r1 ← buildExpressionFromNat x
-- --      r2 ← buildExpressionFromNat y
-- --      returnTC ((λ ass → con (quote _·'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
-- --               appendWithoutRepetition (snd r1) (snd r2))
-- --    buildExpressionFromNat (def (quote _ℕ-_) (x v∷ (con (quote ℕ.suc) (y v∷ [] )) v∷ [])) = do
-- --      r1 ← buildExpressionFromNat x
-- --      r2 ← do y' ← do u1 ← `1` []
-- --                      u2 ← buildExpressionFromNat y
-- --                      returnTC {A = Template × Vars} ((λ ass → con (quote _+'_)
-- --                       (fst u1 ass v∷ fst u2 ass v∷ [])) ,
-- --                           appendWithoutRepetition (snd u1) (snd u2))
-- --              returnTC {A = Template × Vars} ((λ ass → con (quote -'_) (fst y' ass v∷ [])) , snd y')
-- --      returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
-- --               appendWithoutRepetition (snd r1) (snd r2))
-- --    buildExpressionFromNat t' =
-- --     let t = (con (quote ℤ.pos) (t' v∷ []))
-- --     in (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))



-- --    matchTerm : Term → TC (Maybe (Template × Vars))

-- --    matchTerm t@(con (quote ℤ.pos) (x v∷ [])) = do
-- --     just <$> buildExpressionFromNat x
-- --    matchTerm t@(con (quote ℤ.negsuc) (x v∷ [])) =
-- --     do y ← do r1 ← `1` []
-- --               r2 ← buildExpressionFromNat x
-- --               returnTC {A = Template × Vars} ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
-- --                    appendWithoutRepetition (snd r1) (snd r2))
-- --        just <$> returnTC ((λ ass → con (quote -'_) (fst y ass v∷ [])) , snd y)

-- --    matchTerm t@(def (quote -_) xs) = just <$> `-_` xs
-- --    matchTerm t@(def (quote _+_) xs) = just <$> `_+_` xs
-- --    matchTerm t@(def (quote _·_) xs) = just <$> `_·_` xs

-- --    matchTerm _ = returnTC nothing

-- --  private
-- --   module _ (zring : CommRing ℓ-zero) where
-- --    module ETNF = EqualityToNormalform ℤCommRing  ℤCommRing
-- --                   (idCommRingHom _)
-- --    module ETNF≟ = ETNF.Decidable discreteℤ mbNegℤ (just cdℤ) (just ·lCancelℤ) (just ·lCancelℤ)
-- --                    (just (Slowℤ.0≢1-ℤ ∘S sym)) (just (λ _ x → x))
-- --  macro
-- --    ℤ! : Term → TC _
-- --    ℤ! = CommRingSolver.solve!-macro ℤCommRing ℤCommRing (just ·lCancelℤ) fastℤMatcher
-- --        ((quote ℕ._·_) ∷ (quote ℕ._+_) ∷ (quote _+_) ∷ (quote (-_)) ∷ (quote _·_) ∷ (quote _ℕ-_) ∷ [])
-- --        (quote ETNF.solveByDec) (quote ETNF≟.HF-Maybe-prf)
-- --        λ _ → pure true

-- -- module ℚRingSolver where
-- --  open ℚ
-- --  open ℚ'

-- --  ℚMatcher : RingReflectionMatcher
-- --  ℚMatcher .RingReflectionMatcher.mkMatchTermTC _ _ = returnTC matchTerm

-- --   where

-- --   module _ (be : (Term → TC (Template × Vars))) where
-- --    open BE q[ ℚCommRing ] be

-- --    matchTerm : Term → TC (Maybe (Template × Vars))

-- --    matchTerm t@(con (quote SetQuotient.[_]) _) =
-- --       returnTC (just ((λ _ → con (quote K) v[ t ]) , []))

-- --    matchTerm t@(def (quote -_) xs) = just <$> `-_` xs
-- --    matchTerm t@(def (quote _+_) xs) = just <$> `_+_` xs
-- --    matchTerm t@(def (quote _·_) xs) = just <$> `_·_` xs

-- --    matchTerm _ = returnTC nothing

-- --  private
-- --   module _ (zring : CommRing ℓ-zero) where
-- --    module ETNF = EqualityToNormalform ℚCommRing ℚCommRing
-- --                   (idCommRingHom _)
-- --    module ETNF≟ = ETNF.Decidable discreteℚ (λ _ → nothing) nothing nothing nothing
-- --            (just ℚ'.ℚCommRingIsNotZeroRing) (just (λ _ x → x))
-- --  macro
-- --    ℚ! : Term → TC _
-- --    ℚ! = CommRingSolver.solve!-macro ℚCommRing ℚCommRing nothing ℚMatcher
-- --        ((quote ℕ._·_) ∷ (quote ℕ._+_) ∷ (quote _+_) ∷ (quote (-_)) ∷ (quote _·_) ∷ [])
-- --        (quote ETNF.solveByDec) (quote ETNF≟.HF-Maybe-prf)
-- --        λ _ → pure true
