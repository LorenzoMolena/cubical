{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Triple.Base where


open import Cubical.Foundations.Prelude -- renaming (_∎ to _∎≡) -- hiding (step-≡)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP


open import Cubical.Data.Sigma
open import Cubical.Data.Bool.Base


open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv


open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe


open import Cubical.Relation.Nullary.Base


open import Cubical.Relation.Binary.Base


open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Quoset.Base


open import Cubical.Data.Unit.Base renaming (Unit to ⊤ ; tt to ⋆)
open import Cubical.Data.Empty.Base


open Iso
open BinaryRelation


private
  variable
    ℓ ℓ≤ ℓ< : Level


module <-≤-Reasoning 
  (P : Type ℓ) 
  ((posetstr (_≤_) isPoset)   : PosetStr ℓ≤ P) 
  ((quosetstr (_<_) isQuoset) : QuosetStr ℓ< P)
  -- we need it! it is not a weaken, 
  -- it is the same as the one below, but with < and ≤ swapped  
  (<-≤-trans : ∀ x y z → x < y → y ≤ z → x < z) 
  -- should we just assume a <→≤
  -- it can be inferred  
  -- (<→≤ : ∀ x y → x < y → x ≤ y)
  (≤-<-trans : ∀ x y z → x ≤ y → y < z → x < z)
  where


  open IsPoset  -- renaming (is-trans to ≤-trans)
  open IsQuoset -- renaming (is-trans to <-trans)


  private 
    variable
      x y : P


  -- was (ℓ ℓ-⊔ ℓ′ ℓ-⊔ (ℓ-suc ℓ′′) ℓ-⊔ (ℓ-suc ℓ′′′)) 
  record SubRelation {ℓR} (_R_ : Rel P P ℓR ) ℓS ℓIsS : Type (ℓ-max ℓ (ℓ-max ℓR (ℓ-max (ℓ-suc ℓS) (ℓ-suc ℓIsS)))) where
    field
      _S_ : Rel P P ℓS
      IsS : x R y → Type ℓIsS
      IsS? : ∀ (xRy : x R y) → Dec (IsS xRy)
      extract : ∀ {xRy : x R y} → IsS xRy → x S y


  module begin-subrelation-syntax {ℓR ℓS ℓIsS }
    (_R_ : Rel P P ℓR)
    (sub : SubRelation _R_ ℓS ℓIsS)
    where
      open SubRelation sub


      -- True : ∀ {ℓT} {X : Type ℓT} → Dec X → Type
      -- True (yes x) = ⊤
      -- True (no ¬x) = ⊥
      -- 
      -- toWitness : ∀ {ℓT} {X : Type ℓT} {isX? : Dec X} → (True (isX?)) → X
      -- toWitness {isX? = yes x} ⋆ = x  


      infix 1 begin_ 
      begin_ : ∀ {x y} (xRy : x R y) → {s : True (IsS? xRy)} → x S y
      begin_ r {s} = extract (toWitness s)


  ℓ<≤≡ = ℓ-max ℓ (ℓ-max ℓ< ℓ≤) 


  data _<≤≡_ : P → P → Type ℓ<≤≡ where
    strict    : ∀ x y → x < y → x <≤≡ y
    nonstrict : ∀ x y → x ≤ y → x <≤≡ y
    equal     : ∀ x y → x ≡ y → x <≤≡ y


  open SubRelation


  -- was ℓR = ℓ<≤≡
  is<? : SubRelation _<≤≡_ ℓ< ℓ<
  is<? ._S_ = _<_ 
  is<? .IsS {x} {y} = λ where 
                            (strict x y _) → (x < y)
                            (nonstrict _ _ _) → ⊥* 
                            (equal _ _ _) → ⊥* 
  is<? .IsS? (strict _ _ x<y ) = yes x<y
  is<? .IsS? (nonstrict _ _ x) = no λ ()
  is<? .IsS? (equal _ _ x) = no λ () 
  is<? .extract {x} {y} {strict .x .y _} x<y = x<y


  -- Partial order syntax
  module ≤-syntax where
    infixr 2 step-≤
    step-≤ : ∀ (x : P) {y z} → y <≤≡ z → x ≤ y → x <≤≡ z
    step-≤ x (strict _ _ y<z) x≤y = strict x _ (≤-<-trans x _ _ x≤y y<z)
    step-≤ x (nonstrict _ _ y≤z) x≤y = nonstrict x _ 
                                        (isPoset .is-trans x _ _ x≤y y≤z)
    step-≤ x (equal _ _ y≡z) x≤y = nonstrict x _ (subst (x ≤_) y≡z x≤y)


    syntax step-≤ x yRz x≤y = x ≤⟨ x≤y ⟩ yRz


    -- if it ends in a chain of equalities
    infixr 2 step-≤≡
    step-≤≡ : ∀ (x : P) {y z} → y ≡ z → x ≤ y → x <≤≡ z
    step-≤≡ x y≡z x≤y = step-≤ x (equal _ _ y≡z) x≤y
    syntax step-≤≡ x y≡z x≤y = x ≤⟨ x≤y ⟩≡ y≡z


    -- pattern _≤⟨_⟩_ x x<y yRz = step-≤ x yRz x<z 


  -- Strict partial order syntax
  module <-syntax where
    infixr 2 step-<
    step-< : ∀ (x : P) {y z} → y <≤≡ z → x < y → x <≤≡ z
    step-< x (strict _ _ y<z) x<y = strict x _ 
                                    (isQuoset .is-trans x _ _ x<y y<z)
    step-< x (nonstrict _ _ y≤z) x<y = strict x _ (<-≤-trans x _ _ x<y y≤z)
    step-< x (equal _ _ y≡z) x<y = strict x _ (subst (x <_) y≡z x<y)
    syntax step-< x yRz x<y = x <⟨ x<y ⟩ yRz


    -- if it ends in a chain of equalities
    infixr 2 step-<≡
    step-<≡ : ∀ (x : P) {y z} → y ≡ z → x < y → x <≤≡ z
    step-<≡ x y≡z x<y = step-< x (equal _ _ y≡z) x<y
    syntax step-<≡ x y≡z x<y = x <⟨ x<y ⟩≡ y≡z


    -- pattern _<⟨_⟩_ x x<y yRz = step-< x yRz x<z 


  module ≡-syntax where
    -- infixr 2 step-≡
    -- step-≡ : ∀ (x : P) {y z} → y <≤≡ z → x ≡ y → x <≤≡ z
    -- step-≡ x {y} {z} y<≤≡z x≡y = subst (_<≤≡ z) (λ i → x≡y (~ i)) y<≤≡z
    -- syntax step-≡ x yRz x≡y = x ≡⟨ x≡y ⟩ yRz 


    infixr 2 step-≡→≤
    step-≡→≤ : ∀ (x : P) {y z} → y <≤≡ z → x ≡ y → x <≤≡ z
    step-≡→≤ x {y} {z} y<≤≡z x≡y = subst (_<≤≡ z) (λ i → x≡y (~ i)) y<≤≡z
    syntax step-≡→≤ x yRz x≡y = x ≡→≤⟨ x≡y ⟩ yRz 




  -- was {ℓR = ℓ<≤≡} {ℓS = ℓ<} {ℓIsS = ℓ<}
  open begin-subrelation-syntax _<≤≡_ is<?
  open <-syntax
  open ≤-syntax
  open ≡-syntax




  -- step : ∀ {x y z} → y <≤≡ z → x <≤≡ y → x <≤≡ z
  -- step y<≤≡z (strict _ _ x<y) = step-< _ y<≤≡z x<y
  -- step y<≤≡z (nonstrict _ _ x≤y) = step-≤ _ y<≤≡z x≤y
  -- step y<≤≡z (equal _ _ x≡z) = step-≡ _ y<≤≡z x≡z


  infix 3 _◾
  _◾ : ∀ x → x <≤≡ x
  x ◾ = equal x x refl  


  -- pattern _∎ x = equal _ _ (refl {x})


  infixr 2 _≡→≤⟨_]<⟨_⟩_
  _≡→≤⟨_]<⟨_⟩_ : ∀ x {y z w } → (x ≡ y) → (y < z) → z <≤≡ w → x <≤≡ w
  x ≡→≤⟨ x≡y ]<⟨ y<z ⟩ z<≤≡w = x ≡→≤⟨ x≡y ⟩ _ <⟨ y<z ⟩ z<≤≡w
  _≡→≤⟨_≤⟨_⟩≡_ : ∀ x {y z w } → (x ≡ y) → (y ≤ z) → z <≤≡ w → x <≤≡ w
  x ≡→≤⟨ x≡y ≤⟨ y≤z ⟩≡ z<≤≡w = x ≡→≤⟨ x≡y ⟩ _ ≤⟨ y≤z ⟩ z<≤≡w


  infixl 5 _≡→≤⟨_]◾ 
  _≡→≤⟨_]◾ : ∀ x {y} → (x ≡ y) → x <≤≡ y
  x ≡→≤⟨ x≡y ]◾  = x ≡→≤⟨ x≡y ⟩ _ ◾


  infixr 2 _⟩≡[_ 
  _⟩≡[_ : {x y z : P} → x ≡ y → y ≡ z → x ≡ z
  _⟩≡[_ {x = x} x≡y y≡z = x ≡⟨ x≡y ⟩ y≡z  


  -- syntax ⟩syntax y x≡y = x≡y ⟩≡ y


  ≡⟨⟩syntax : (x y : P) → x ≡ y → x ≡ y  
  ≡⟨⟩syntax x y x≡y = x≡y


  syntax ≡⟨⟩syntax x y x≡y = x ≡⟨ x≡y ⟩≡ y


-- 
  -- ■-syntax : ∀ {x y : P} → (z : P) → (x<≤≡y : x <≤≡ y) → (y<≤≡z : y <≤≡ z) → {True (IsS? is<? (step y<≤≡z x<≤≡y))} → x < z
  -- ■-syntax z x<≤≡y (strict _ .z y<z)    {s} = begin_ (_ <⟨ y<z ⟩ z ∎) {s}
  -- ■-syntax z x<≤≡y (nonstrict _ .z y≤z) {s} = begin_ {!   !} {{! s  !}}
  -- ■-syntax z x<≤≡y (equal _ .z y≡z)     {s} = {!   !}


  -- syntax ■-syntax y x<≤≡y = x<≤≡y y ■ 
 -- 
 -- _<⟨_⟩_ : (x : P) {y z : P} → x < y → y <≤≡ z → x < z
 -- -- x <⟨ p ⟩ q = isQuoset .is-trans x _ _ p q
 -- x <⟨ x<y ⟩ strict    _ _ y<z = <-trans isQuoset x _ _ x<y y<z
 -- x <⟨ x<y ⟩ nonstrict _ _ y≤z = <-≤-trans x _ _ x<y y≤z
 -- x <⟨ x<y ⟩ equal     _ _ y≡z = subst (x <_) y≡z x<y
 -- 
 -- _<≤≡⟨_⟩_ : (x : P) {y z : P} → x <≤≡ y → y < z → x < z
 -- x <≤≡⟨ strict    x _ x<y ⟩ y<z = <-trans isQuoset x _ _ x<y y<z
 -- x <≤≡⟨ nonstrict x _ x≤y ⟩ y<z = ≤-<-trans x _ _ x≤y y<z
 -- x <≤≡⟨ equal     x _ x≡y ⟩ y<z = subst (_< _) (λ i → x≡y (~ i)) y<z 


 -- isStrict : Dec


  example : ∀ (x y z u v w α γ δ : P) 
          → x < y 
          → y ≤ z 
          → z ≡ u 
          → u < v 
          → v ≤ w 
          → w ≡ α
          → α ≡ γ
          → γ ≡ δ
          → x < δ  
  example x y z u v w α γ δ x<y y≤z z≡u u<v v≤w w≡α α≡γ γ≡δ = begin 
        x   <⟨   x<y      ⟩ 
        y   ≤⟨   y≤z      ⟩ 
        z   ≡→≤⟨ z≡u      ⟩ 
        u   <⟨   u<v      ⟩ 
        v   ≤⟨   v≤w      ⟩≡ 
        w   ≡⟨   w≡α      ⟩ 
        α   ≡⟨   α≡γ      ⟩ 
        γ   ≡[ i ]⟨ γ≡δ i ⟩ 
        δ   ∎


   -- isStrict : Dec 
  example′ : ∀ (x y z u v w α γ δ : P) 
          → x < y 
          → y ≤ z 
          → z ≡ u 
          → u < v 
          → v ≤ w 
          → w ≡ α
          → α ≡ γ
          → γ ≡ δ
          → x < δ  
  example′ x y z u v w α γ δ x<y y≤z z≡u u<v v≤w w≡α α≡γ γ≡δ = begin 
        x   <⟨   x<y      ⟩ 
        y   ≤⟨   y≤z      ⟩ 
        z   ≡→≤⟨ z ≡⟨ z≡u        ⟩ 
                 u ≡⟨ sym z≡u    ⟩ 
                 z ≡[ i ]⟨ z≡u i ⟩ 
                 u ∎     ⟩ 
        u   <⟨   u<v      ⟩ 
        v   ≤⟨   v≤w      ⟩ 
        w   ≡→≤⟨ 
                w   ≡⟨ w≡α ⟩ 
                α   ≡⟨ α≡γ ⟩ 
                γ   ≡[ i ]⟨ γ≡δ i ⟩ 
                δ   ∎ 
              ⟩ 
        δ ◾


  example′′ : ∀ (x y z u v w : P) 
          → x < y 
          → y ≤ z 
          → z ≡ u 
          → u < v 
          → v ≤ w 
          → x < w  
  example′′ x y z u v w x<y y≤z z≡u u<v v≤w = begin 
     x  <⟨ x<y ⟩ 
     y  ≤⟨ y≤z ⟩ 
     z  ≡→≤⟨ z≡u ⟩≡[        -- syntax to start a chain of equalities
     u  ≡⟨ sym z≡u ⟩        -- from Prelude
     z  ≡⟨ z≡u ⟩            -- from Prelude
     u  ≡[ i ]⟨ z≡u (~ i) ⟩ -- from Prelude
     z  ≡⟨ z≡u ⟩≡           -- not from Prelude, but it just return z≡u (to remove _■ )
     u  ]<⟨ u<v ⟩           -- syntax to link a chain of equalities to a <
     v  ≤⟨ v≤w ⟩ 
     w  ◾ 


     -- the limitation is that we can't use methods from Prelude in the last step, 
     -- like x ≡[ i ]⟨ p i ⟩ y 
     -- we could just rewrite all those functions without the ■ , but maybe there are 
     -- better options   


  -- syntax step-< x (equal y≡z) x<y = x <⟨ x<y ⟩-step≡ y≡z
  -- x <⟨ x<y ⟩ (equal y≡z)  


  -- example′ : ∀ (x y z u v w : P) 
  --         → x ≡ y 
  --         → y ≤ z 
  --         → z ≡ u 
  --         → u < v 
  --         → v ≤ w 
  --         → x < w 
  -- example′ x y z u v w x≡y y≤z z≡u u<v v≤w = begin 
  --   x ≡⟨ x≡y ⟩ 
  --   y ≤⟨ y≤z ⟩ 
  --   z ≡⟨ z≡u ⟩ 
  --   u <⟨ u<v ⟩ 
  --   v ≤⟨ v≤w ⟩ 
  --   w ∎






  -- pattern x <<⟨ x<y ⟩ q = _<≤≡⟨_⟩_ x (strict _ _ x<y) q


 -- _<-≤⟨_⟩_ : (x : P) {y z : P} → x < y → y ≤ z → x < z
 -- x <-≤⟨ p ⟩ q = <-≤-trans x _ _ p q


 -- _<⟨_⟩_<-≤⟨_⟩_ : (x : P) → {z w : P} → x < y → y ≤ z → x < z






-- 
 -- <◾-syntax : (x y : P) → x < y → x < y
 -- <◾-syntax x y p = p
 -- syntax <◾-syntax x y p = x <⟨ p ⟩ y ◾< 
-- 
 -- infixr 0 _<⟨_⟩_
 -- infixr 1 <◾-syntax

