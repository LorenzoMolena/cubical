{-# OPTIONS --safe #-}
module Cubical.Data.Int.Fast.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.NatPlusOne.Base as ℕ₊₁
open import Cubical.Data.Nat as ℕ
  hiding   (+-assoc ; +-comm ; min ; max ; minComm ; maxComm)
  renaming (_·_ to _·ℕ_; _+_ to _+ℕ_ ; ·-assoc to ·ℕ-assoc ;
            ·-comm to ·ℕ-comm ; isEven to isEvenℕ ; isOdd to isOddℕ)
open import Cubical.Data.Sum
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties


open import Cubical.Data.Int.Base as ℤ hiding (_+_ ; _·_ ; _-_) renaming (_+f_ to _+_ ; _·f_ to _·_ ; _-f_ to _-_)
open import Cubical.Data.Int.Properties as P public
 hiding (·lCancel ; ·rCancel; +Assoc ;+Comm;-DistL·;-DistR·;minusPlus;plusMinus
   ;·Assoc;·Comm;·DistL+;·DistR+;·IdL;·IdR;·DistPosRMin;·DistPosRMax;·DistPosLMin;·DistPosLMax;abs·
   ; inj-z+ ; 
   -- functions/properties rewritten in a different way (hopefully faster)
   min ; minComm ; minIdem ; max ; maxComm ; maxIdem ; 
   sucPred ; predSuc ; 
   sucDistMin ; predDistMin ; minSucL ; minSucR ; minPredL ; minPredR ; 
   sucDistMax ; predDistMax ; maxSucL ; maxSucR ; maxPredL ; maxPredR ;
   -- these don't need to be rewritten (except for a space in predℤ+pos) :
   injPos ; injNegsuc ; posNotnegsuc ; negsucNotpos ; injNeg ; discreteℤ ; isSetℤ ;
   -pos ; -neg ; sucℤnegsucneg ; -sucℤ ; -predℤ ; -Involutive ; isEquiv- ;
   sucℤ+pos ; predℤ+negsuc ; sucℤ+negsuc ; predℤ+pos ; predℤ-pos ;
   -- properties of +f/·f/-f etc.
   predℤ+ ; +predℤ ; sucℤ+ ; +sucℤ ; pos0+ ; negsuc0+ ;
   -- these don't need to be rewritten
   ind-comm ; ind-assoc
   )

open import Cubical.Data.Int.Order as P public
  hiding (<-+-≤; <-+o; <-o+; <-o+-cancel; <-pos+-trans; <Monotone+; ≤-+o; ≤-+o-cancel; ≤-o+; ≤-o+-cancel; ≤-pos+-trans; ≤Monotone+; ≤SumRightPos; 0<o→≤-·o-cancel; 0≤o→≤-·o; 0≤x²; ·suc≤0; ≤-o·-cancel; ≤-·o; ≤-·o-cancel; 0<o→<-·o; 0<o→<-·o-cancel; <-o·-cancel; <-·o; <-·o-cancel; ·suc<0; ·0<; 0<·ℕ₊₁; +0<; 0<→ℕ₊₁)

subst-f : (A : (ℤ → ℤ → ℤ) → (ℤ → ℤ → ℤ) → Type) → A ℤ._+_ ℤ._·_ → A _+_ _·_
subst-f A = subst2 A (λ i x y → +≡+f x y i) (λ i x y → ·≡·f x y i)

-- open import Cubical.Algebra.CommRing
-- open import Cubical.Algebra.Ring.Properties
-- open import Cubical.Algebra.Ring
-- 
-- 
-- ℤCommRing : CommRing ℓ-zero
-- ℤCommRing .fst = ℤ
-- ℤCommRing .snd .CommRingStr.0r = 0
-- ℤCommRing .snd .CommRingStr.1r = 1
-- ℤCommRing .snd .CommRingStr._+_ = _+_
-- ℤCommRing .snd .CommRingStr._·_ = _·_
-- CommRingStr.- ℤCommRing .snd = -_
-- ℤCommRing .snd .CommRingStr.isCommRing = isCommRingℤ'
--   where
--   abstract
--     isCommRingℤ : IsCommRing (pos 0) (pos 1) ℤ._+_ ℤ._·_ (-_)
--     isCommRingℤ =
--       makeIsCommRing isSetℤ P.+Assoc (λ _ → refl)
--                                  P.-Cancel P.+Comm P.·Assoc
--                                  P.·IdR P.·DistR+ P.·Comm
-- 
--     isCommRingℤ' : IsCommRing (pos 0) (pos 1) _+_ _·_ (-_)
--     isCommRingℤ' =
--      subst-f (λ _+_ _·_ → IsCommRing (pos 0) (pos 1) _+_ _·_ (-_))
--        isCommRingℤ


-- open RingTheory (CommRing→Ring ℤCommRing) public
-- open CommRingTheory (ℤCommRing) public using ()
-- open RingStr (snd (CommRing→Ring ℤCommRing)) public
-- open CommRingStr (snd (ℤCommRing)) public hiding (_·_;-_;_+_;_-_)

sucℤ[negsuc]-pos : ∀ k → sucℤ (negsuc k) ≡ - pos k 
sucℤ[negsuc]-pos zero = refl
sucℤ[negsuc]-pos (suc k) = refl

+IdL : ∀ z → 0 + z ≡ z
+IdL (pos n)    = refl
+IdL (negsuc n) = refl

+IdR : ∀ z → z + 0 ≡ z
+IdR (pos n)    = cong pos (+-zero n)
+IdR (negsuc n) = refl

sucℤ+pos-f : ∀ n m → sucℤ (m + pos n) ≡ (sucℤ m) + pos n
sucℤ+pos-f n (pos n₁)                  = refl
sucℤ+pos-f zero (negsuc n₁)            = sym (+IdR (sucℤ (negsuc n₁ + pos zero)))
sucℤ+pos-f (suc zero) (negsuc zero)    = refl
sucℤ+pos-f (suc (suc n)) (negsuc zero) = cong (sucℤ ∘ (ℕ-f-hlp (suc n))) (zero∸ (suc n))
sucℤ+pos-f (suc n) (negsuc (suc n₁))   = w n n₁ where
  w : ∀ n m → sucℤ (ℕ-f-hlp (n ∸ suc m) (suc m ∸ n)) ≡ ℕ-f-hlp (n ∸ m) (m ∸ n)
  w zero zero          = refl
  w zero (suc m)       = refl
  w (suc zero) zero    = refl
  w (suc (suc n)) zero = cong (sucℤ ∘ (ℕ-f-hlp (suc n))) (zero∸ (suc n))
  w (suc n) (suc m)    = w n m

·lCancel : (c m n : ℤ) → c · m ≡ c · n → ¬ c ≡ 0 → m ≡ n
·lCancel c m n = subst-f
  (λ _+_ _·_ → c · m ≡ c · n → ¬ c ≡ 0 → m ≡ n) (P.·lCancel c m n)

·rCancel : (c m n : ℤ) → m · c ≡ n · c → ¬ c ≡ 0 → m ≡ n
·rCancel c m n = subst-f
  (λ _+_ _·_ → m · c ≡ n · c → ¬ c ≡ 0 → m ≡ n) (P.·rCancel c m n)

·DistPosRMin : (x : ℕ) (y z : ℤ) → pos x · P.min y z ≡ P.min (pos x · y) (pos x · z)
·DistPosRMin x y z = subst-f
  (λ _+_ _·_ → pos x · P.min y z ≡ P.min (pos x · y) (pos x · z)) (P.·DistPosRMin x y z)

·DistPosRMax : (x : ℕ) (y z : ℤ) → pos x · P.max y z ≡ P.max (pos x · y) (pos x · z)
·DistPosRMax x y z = subst-f
  (λ _+_ _·_ → pos x · P.max y z ≡ P.max (pos x · y) (pos x · z)) (P.·DistPosRMax x y z)

·DistPosLMin : (x y : ℤ) (z : ℕ) → P.min x y · pos z ≡ P.min (x · pos z) (y · pos z)
·DistPosLMin x y z = subst-f
  (λ _+_ _·_ → P.min x y · pos z ≡ P.min (x · pos z) (y · pos z)) (P.·DistPosLMin x y z)

·DistPosLMax : (x y : ℤ) (z : ℕ) → P.max x y · pos z ≡ P.max (x · pos z) (y · pos z)
·DistPosLMax x y z = subst-f
  (λ _+_ _·_ → P.max x y · pos z ≡ P.max (x · pos z) (y · pos z)) (P.·DistPosLMax x y z)

inj-z+ : ∀ {z l n} → z + l ≡ z + n → l ≡ n
inj-z+ {z} {l} {n} =
 subst-f
  (λ _+_ _·_ → z + l ≡ z + n → l ≡ n) (P.inj-z+ {z} {l} {n})

<-+-≤ : {m n o s : ℤ} → m < n → o ≤ s → m + o < n + s
<-+-≤ {m} {n} {o} {s} = subst-f
  (λ _+_ _·_ → m < n → o ≤ s → m + o < n + s) (P.<-+-≤ {m} {n} {o} {s})

<-+o : {m n o : ℤ} → m < n → m + o < n + o
<-+o {m} {n} {o} = subst-f
  (λ _+_ _·_ → m < n → m + o < n + o) (P.<-+o {m} {n} {o})

<-o+ : {m n o : ℤ} → m < n → o + m < o + n
<-o+ {m} {n} {o} = subst-f
  (λ _+_ _·_ → m < n → o + m < o + n) (P.<-o+ {m} {n} {o})

<-o+-cancel : {o m n : ℤ} → o + m < o + n → m < n
<-o+-cancel {o} {m} {n} = subst-f
  (λ _+_ _·_ → o + m < o + n → m < n) (P.<-o+-cancel {o} {m} {n})

<-o·-cancel : {k : ℕ} {m n : ℤ} → m + pos k · m < n + pos k · n → m < n
<-o·-cancel {k} {m} {n} = subst-f
  (λ _+_ _·_ → m + (pos k · m) < n + (pos k · n) → m < n) (P.<-o·-cancel {k} {m} {n})

<-pos+-trans : {k : ℕ} {m n : ℤ} → pos k + m < n → m < n
<-pos+-trans {k} {m} {n} = subst-f
  (λ _+_ _·_ → pos k + m < n → m < n) (P.<-pos+-trans {k} {m} {n})

<Monotone+ : {m n o s : ℤ} → m < n → o < s → m + o < n + s
<Monotone+ {m} {n} {o} {s} = subst-f
  (λ _+_ _·_ → m < n → o < s → m + o < n + s) (P.<Monotone+ {m} {n} {o} {s})

≤-+o : {m n o : ℤ} → m ≤ n → m + o ≤ n + o
≤-+o {m} {n} {o} = subst-f
  (λ _+_ _·_ → m ≤ n → m + o ≤ n + o) (P.≤-+o {m} {n} {o})

≤-+o-cancel : {m o n : ℤ} → m + o ≤ n + o → m ≤ n
≤-+o-cancel {m} {o} {n} = subst-f
  (λ _+_ _·_ → m + o ≤ n + o → m ≤ n) (P.≤-+o-cancel {m} {o} {n})

≤-o+ : {m n o : ℤ} → m ≤ n → o + m ≤ o + n
≤-o+ {m} {n} {o} = subst-f
  (λ _+_ _·_ → m ≤ n → o + m ≤ o + n) (P.≤-o+ {m} {n} {o})

≤-o+-cancel : {o m n : ℤ} → o + m ≤ o + n → m ≤ n
≤-o+-cancel {o} {m} {n} = subst-f
  (λ _+_ _·_ → o + m ≤ o + n → m ≤ n) (P.≤-o+-cancel {o} {m} {n})

≤-o·-cancel : {k : ℕ} {m n : ℤ} → m + pos k · m ≤ n + pos k · n → m ≤ n
≤-o·-cancel {k} {m} {n} = subst-f
  (λ _+_ _·_ → m + (pos k · m) ≤ n + (pos k · n) → m ≤ n) (P.≤-o·-cancel {k} {m} {n})

≤-pos+-trans : {k : ℕ} {m n : ℤ} → pos k + m ≤ n → m ≤ n
≤-pos+-trans {k} {m} {n} = subst-f
  (λ _+_ _·_ → pos k + m ≤ n → m ≤ n) (P.≤-pos+-trans {k} {m} {n})

≤Monotone+ : {m n o s : ℤ} → m ≤ n → o ≤ s → m + o ≤ n + s
≤Monotone+ {m} {n} {o} {s} = subst-f
  (λ _+_ _·_ → m ≤ n → o ≤ s → m + o ≤ n + s) (P.≤Monotone+ {m} {n} {o} {s})

≤SumRightPos : {n : ℤ} {k : ℕ} → n ≤ pos k + n
≤SumRightPos {n} {k} = subst-f
  (λ _+_ _·_ → n ≤ pos k + n) (P.≤SumRightPos {n} {k})

0<o→≤-·o-cancel : {o m n : ℤ} → pos 0 < o → m · o ≤ n · o → m ≤ n
0<o→≤-·o-cancel {o} {m} {n} = subst-f
  (λ _+_ _·_ → pos 0 < o → m · o ≤ n · o → m ≤ n) (P.0<o→≤-·o-cancel {o} {m} {n})

0≤o→≤-·o : {o m n : ℤ} → pos 0 ≤ o → m ≤ n → m · o ≤ n · o
0≤o→≤-·o {o} {m} {n} = subst-f
  (λ _+_ _·_ → pos 0 ≤ o → m ≤ n → m · o ≤ n · o) (P.0≤o→≤-·o {o} {m} {n})

0≤x² : (n : ℤ) → pos 0 ≤ n · n
0≤x² n = subst-f
  (λ _+_ _·_ → pos 0 ≤ n · n) (P.0≤x² n)

·suc≤0 : {m : ℤ} {k : ℕ} → m · pos (suc k) ≤ pos 0 → m ≤ pos 0
·suc≤0 {m} {k} = subst-f
  (λ _+_ _·_ → m · pos (suc k) ≤ pos 0 → m ≤ pos 0) (P.·suc≤0 {m} {k})

≤-·o : {m n : ℤ} {k : ℕ} → m ≤ n → m · pos k ≤ n · pos k
≤-·o {m} {n} {k} = subst-f
  (λ _+_ _·_ → m ≤ n → m · pos k ≤ n · pos k) (P.≤-·o {m} {n} {k})

≤-·o-cancel : {m : ℤ} {k : ℕ} {n : ℤ} → m · pos (suc k) ≤ n · pos (suc k) → m ≤ n
≤-·o-cancel {m} {k} {n} = subst-f
  (λ _+_ _·_ → m · pos (suc k) ≤ n · pos (suc k) → m ≤ n) (P.≤-·o-cancel {m} {k} {n})

0<o→<-·o : {o m n : ℤ} → pos 0 < o → m < n → m · o < n · o
0<o→<-·o {o} {m} {n} = subst-f
  (λ _+_ _·_ → pos 0 < o → m < n → m · o < n · o) (P.0<o→<-·o {o} {m} {n})

0<o→<-·o-cancel : {o m n : ℤ} → pos 0 < o → m · o < n · o → m < n
0<o→<-·o-cancel {o} {m} {n} = subst-f
  (λ _+_ _·_ → pos 0 < o → m · o < n · o → m < n) (P.0<o→<-·o-cancel {o} {m} {n})


<-·o : {m n : ℤ} {k : ℕ} → m < n → m · pos (suc k) < n · pos (suc k)
<-·o {m} {n} {k} = subst-f
  (λ _+_ _·_ → m < n → m · pos (suc k) < n · pos (suc k)) (P.<-·o {m} {n} {k})

<-·o-cancel : {m : ℤ} {k : ℕ} {n : ℤ} → m · pos (suc k) < n · pos (suc k) → m < n
<-·o-cancel {m} {k} {n} = subst-f
  (λ _+_ _·_ → m · pos (suc k) < n · pos (suc k) → m < n) (P.<-·o-cancel {m} {k} {n})

·suc<0 : {m : ℤ} {k : ℕ} → m · pos (suc k) < pos 0 → m < pos 0
·suc<0 {m} {k} = subst-f
  (λ _+_ _·_ → m · pos (suc k) < pos 0 → m < pos 0) (P.·suc<0 {m} {k})

·0< : ∀ m n → 0< m → 0< n → 0< (m · n)
·0< m n p q = subst-f
  (λ _+_ _·_ → 0< m → 0< n → 0< (m · n))
  (P.·0< m n) p q

0<·ℕ₊₁ : ∀ m n → 0< (m · pos (ℕ₊₁→ℕ n)) → 0< m
0<·ℕ₊₁ m n x = subst-f
  (λ _+_ _·_ → 0< (m · pos (ℕ₊₁→ℕ n)) → 0< m)
  (P.0<·ℕ₊₁ m n) x

+0< : ∀ m n → 0< m → 0< n → 0< (m + n)
+0< m n p q = subst-f
  (λ _+_ _·_ → 0< m → 0< n → 0< (m + n))
  (P.+0< m n) p q

0<→ℕ₊₁ : ∀ n → 0< n → Σ ℕ₊₁ λ m → n ≡ pos (ℕ₊₁→ℕ m)
0<→ℕ₊₁ n x = subst-f
  (λ _+_ _·_ → Σ ℕ₊₁ λ m → n ≡ pos (ℕ₊₁→ℕ m))
  (P.0<→ℕ₊₁ n x)


abs· : (m n : ℤ) → abs (m · n) ≡ abs m ·ℕ abs n
abs· (pos m) (pos n) = refl
abs· (pos zero) (negsuc n) = refl
abs· (pos (suc m)) (negsuc n) = refl
abs· (negsuc m) (pos zero) = 0≡m·0 m
abs· (negsuc m) (pos (suc n)) = refl
abs· (negsuc m) (negsuc n) = refl

-1·x≡-x : ∀ x → -1 · x ≡ - x
-1·x≡-x (pos zero) = refl
-1·x≡-x (pos (suc n)) = cong negsuc (+-zero n)
-1·x≡-x (negsuc n) = cong (pos ∘ suc) (+-zero n)


_≤'_ : ℤ → ℤ → Type₀
m ≤' n = Σ[ k ∈ ℕ ] m + pos k ≡ n

_<'_ : ℤ → ℤ → Type₀
m <' n = sucℤ m ≤' n

-- functions/properies added :

min : ℤ → ℤ → ℤ
min (pos m)    (pos n)    = pos (ℕ.min m n)
min (pos m)    (negsuc n) = negsuc n
min (negsuc m) (pos n)    = negsuc m
min (negsuc m) (negsuc n) = negsuc (ℕ.max m n)

minComm : ∀ n m → min n m ≡ min m n
minComm (pos m)    (pos n)    = cong pos (ℕ.minComm m n)
minComm (pos m)    (negsuc n) = refl
minComm (negsuc m) (pos n)    = refl
minComm (negsuc m) (negsuc n) = cong negsuc (ℕ.maxComm m n)

-- To move into Nat.Properties:
ℕminIdem : ∀ n → ℕ.min n n ≡ n
ℕminIdem zero    = refl
ℕminIdem (suc n) = cong suc (ℕminIdem n)

ℕmaxIdem : ∀ n → ℕ.max n n ≡ n
ℕmaxIdem zero    = refl
ℕmaxIdem (suc n) = cong suc (ℕmaxIdem n)
-- -----

-- To move into Nat.Properties:
-- test for faster min
open import Agda.Builtin.Bool as B using ()
open import Agda.Builtin.Nat using () renaming ( _<_ to _<ᵇ_ )  

ℕmin' : ℕ → ℕ → ℕ
ℕmin' m n with (m <ᵇ n)
...          | B.false = n
...          | B.true  = m
-- -----

-- _ : ℕ.min 9008019290921 1000000000 ≡ 1000000000
-- _ = refl 



minIdem : ∀ n → min n n ≡ n
minIdem (pos n)    = cong pos (ℕminIdem n)
minIdem (negsuc n) = cong negsuc (ℕmaxIdem n)

max : ℤ → ℤ → ℤ
max (pos m)    (pos n)    = pos (ℕ.max m n )
max (pos m)    (negsuc n) = pos m
max (negsuc m) (pos n)    = pos n
max (negsuc m) (negsuc n) = negsuc (ℕ.min m n)

maxComm : ∀ m n → max m n ≡ max n m 
maxComm (pos m)    (pos n)    = cong pos (ℕ.maxComm m n)
maxComm (pos m)    (negsuc n) = refl
maxComm (negsuc m) (pos n)    = refl
maxComm (negsuc m) (negsuc n) = cong negsuc (ℕ.minComm m n)

maxIdem : ∀ n → max n n ≡ n 
maxIdem (pos n)    = cong pos (ℕmaxIdem n)
maxIdem (negsuc n) = cong negsuc (ℕminIdem n)

sucPred : ∀ n → sucℤ (predℤ n) ≡ n
sucPred (pos zero)    = refl
sucPred (pos (suc n)) = refl
sucPred (negsuc n)    = refl

predSuc : ∀ n → predℤ (sucℤ n) ≡ n
predSuc (pos n)          = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

sucDistMin : ∀ m n → sucℤ (min m n) ≡ min (sucℤ m) (sucℤ n)
sucDistMin (pos m)          (pos n)          = refl
sucDistMin (pos zero)       (negsuc zero)    = refl
sucDistMin (pos zero)       (negsuc (suc n)) = refl
sucDistMin (pos (suc m))    (negsuc zero)    = refl
sucDistMin (pos (suc m))    (negsuc (suc n)) = refl
sucDistMin (negsuc zero)    (pos n)          = refl
sucDistMin (negsuc (suc m)) (pos n)          = refl
sucDistMin (negsuc zero)    (negsuc zero)    = refl
sucDistMin (negsuc zero)    (negsuc (suc n)) = refl
sucDistMin (negsuc (suc m)) (negsuc zero)    = refl
sucDistMin (negsuc (suc m)) (negsuc (suc n)) = refl

predDistMin : ∀ m n → predℤ (min m n) ≡ min (predℤ m) (predℤ n)
predDistMin (pos zero)    (pos zero)    = refl
predDistMin (pos zero)    (pos (suc n)) = refl
predDistMin (pos (suc m)) (pos zero)    = refl
predDistMin (pos (suc m)) (pos (suc n)) = refl
predDistMin (pos zero)    (negsuc n)    = refl
predDistMin (pos (suc m)) (negsuc n)    = refl
predDistMin (negsuc m)    (pos zero)    = refl
predDistMin (negsuc m)    (pos (suc n)) = refl
predDistMin (negsuc m)    (negsuc n)    = refl

-- to move in Nat.Properties:
ℕminSucL : ∀ n → ℕ.min (suc n) n ≡ n
ℕminSucL zero    = refl
ℕminSucL (suc n) = cong suc (ℕminSucL n)

ℕminSucR : ∀ n → ℕ.min n (suc n) ≡ n
ℕminSucR zero    = refl
ℕminSucR (suc n) = cong suc (ℕminSucR n)

ℕmaxSucL : ∀ n → ℕ.max (suc n) n ≡ suc n
ℕmaxSucL zero    = refl
ℕmaxSucL (suc n) = cong suc (ℕmaxSucL n)

ℕmaxSucR : ∀ n → ℕ.max n (suc n) ≡ suc n
ℕmaxSucR zero    = refl
ℕmaxSucR (suc n) = cong suc (ℕmaxSucR n)
-- ----

minSucL : ∀ m → min (sucℤ m) m ≡ m
minSucL (pos m)          = cong pos (ℕminSucL m)
minSucL (negsuc zero)    = refl
minSucL (negsuc (suc m)) = cong negsuc (ℕmaxSucR m)

minSucR : ∀ m → min m (sucℤ m)  ≡ m
minSucR m = minComm m (sucℤ m) ∙ minSucL m

minPredL : ∀ m → min (predℤ m) m ≡ predℤ m
minPredL (pos zero)    = refl
minPredL (pos (suc m)) = cong pos (ℕminSucR m)
minPredL (negsuc m)    = cong negsuc (ℕmaxSucL m)

minPredR : ∀ m → min m (predℤ m) ≡ predℤ m
minPredR m = minComm m (predℤ m) ∙ minPredL m

sucDistMax : ∀ m n → sucℤ (max m n) ≡ max (sucℤ m) (sucℤ n)
sucDistMax (pos m)          (pos n)          = refl
sucDistMax (pos m)          (negsuc zero)    = refl
sucDistMax (pos m)          (negsuc (suc n)) = refl
sucDistMax (negsuc zero)    (pos n)          = refl
sucDistMax (negsuc (suc m)) (pos n)          = refl
sucDistMax (negsuc zero)    (negsuc zero)    = refl
sucDistMax (negsuc zero)    (negsuc (suc n)) = refl
sucDistMax (negsuc (suc m)) (negsuc zero)    = refl
sucDistMax (negsuc (suc m)) (negsuc (suc n)) = refl

predDistMax : ∀ m n → predℤ (max m n) ≡ max (predℤ m) (predℤ n)
predDistMax (pos zero)    (pos zero)    = refl
predDistMax (pos zero)    (pos (suc n)) = refl
predDistMax (pos (suc m)) (pos zero)    = refl
predDistMax (pos (suc m)) (pos (suc n)) = refl
predDistMax (pos zero)    (negsuc n)    = refl
predDistMax (pos (suc m)) (negsuc n)    = refl
predDistMax (negsuc m)    (pos zero)    = refl
predDistMax (negsuc m)    (pos (suc n)) = refl
predDistMax (negsuc m)    (negsuc n)    = refl

maxSucL : ∀ m → max (sucℤ m) m ≡ sucℤ m
maxSucL (pos m)          = cong pos (ℕmaxSucL m)
maxSucL (negsuc zero)    = refl
maxSucL (negsuc (suc m)) = cong negsuc (ℕminSucR m)

maxSucR : ∀ m → max m (sucℤ m) ≡ sucℤ m
maxSucR m = maxComm m (sucℤ m) ∙ maxSucL m

maxPredL : ∀ m → max (predℤ m) m ≡ m
maxPredL (pos zero)    = refl
maxPredL (pos (suc m)) = cong pos (ℕmaxSucR m)
maxPredL (negsuc m)    = cong negsuc (ℕminSucL m)

maxPredR : ∀ m → max m (predℤ m) ≡ m
maxPredR m = maxComm m (predℤ m) ∙ maxPredL m

injPos : ∀ {a b : ℕ} → pos a ≡ pos b → a ≡ b
injPos {a} h = subst T h refl
  where
  T : ℤ → Type₀
  T (pos x)    = a ≡ x
  T (negsuc _) = ⊥

injNegsuc : ∀ {a b : ℕ} → negsuc a ≡ negsuc b → a ≡ b
injNegsuc {a} h = subst T h refl
  where
  T : ℤ → Type₀
  T (pos _) = ⊥
  T (negsuc x) = a ≡ x

posNotnegsuc : ∀ (a b : ℕ) → ¬ (pos a ≡ negsuc b)
posNotnegsuc a b h = subst T h 0
  where
  T : ℤ → Type₀
  T (pos _)    = ℕ
  T (negsuc _) = ⊥

negsucNotpos : ∀ (a b : ℕ) → ¬ (negsuc a ≡ pos b)
negsucNotpos a b h = subst T h 0
  where
  T : ℤ → Type₀
  T (pos _)    = ⊥
  T (negsuc _) = ℕ

injNeg : ∀ {a b : ℕ} → neg a ≡ neg b → a ≡ b
injNeg {zero} {zero} _ = refl
injNeg {zero} {suc b} nega≡negb = ⊥.rec (posNotnegsuc 0 b nega≡negb)
injNeg {suc a} {zero} nega≡negb = ⊥.rec (negsucNotpos a 0 nega≡negb)
injNeg {suc a} {suc b} nega≡negb = cong suc (injNegsuc nega≡negb)

discreteℤ : Discrete ℤ
discreteℤ (pos n) (pos m) with discreteℕ n m
... | yes p = yes (cong pos p)
... | no p  = no (λ x → p (injPos x))
discreteℤ (pos n) (negsuc m) = no (posNotnegsuc n m)
discreteℤ (negsuc n) (pos m) = no (negsucNotpos n m)
discreteℤ (negsuc n) (negsuc m) with discreteℕ n m
... | yes p = yes (cong negsuc p)
... | no p  = no (λ x → p (injNegsuc x))

isSetℤ : isSet ℤ
isSetℤ = Discrete→isSet discreteℤ

-pos : ∀ n → - (pos n) ≡ neg n
-pos zero    = refl
-pos (suc n) = refl

-neg : ∀ n → - (neg n) ≡ pos n
-neg zero    = refl
-neg (suc n) = refl

sucℤnegsucneg : ∀ n → sucℤ (negsuc n) ≡ neg n
sucℤnegsucneg zero    = refl
sucℤnegsucneg (suc n) = refl

-sucℤ : ∀ n → - sucℤ n ≡ predℤ (- n)
-sucℤ (pos zero)       = refl
-sucℤ (pos (suc n))    = refl
-sucℤ (negsuc zero)    = refl
-sucℤ (negsuc (suc n)) = refl

-predℤ : ∀ n → - predℤ n ≡ sucℤ (- n)
-predℤ (pos zero)       = refl
-predℤ (pos (suc n))    = -pos n ∙ sym (sucℤnegsucneg n)
-predℤ (negsuc zero)    = refl
-predℤ (negsuc (suc n)) = refl

-Involutive : ∀ z → - (- z) ≡ z
-Involutive (pos n)    = cong -_ (-pos n) ∙ -neg n
-Involutive (negsuc n) = refl

isEquiv- : isEquiv (-_)
isEquiv- = isoToIsEquiv (iso -_ -_ -Involutive -Involutive)

sucℤ+pos : ∀ n m → sucℤ (m +pos n) ≡ (sucℤ m) +pos n
sucℤ+pos zero m = refl
sucℤ+pos (suc n) m = cong sucℤ (sucℤ+pos n m)

predℤ+negsuc : ∀ n m → predℤ (m +negsuc n) ≡ (predℤ m) +negsuc n
predℤ+negsuc zero m = refl
predℤ+negsuc (suc n) m = cong predℤ (predℤ+negsuc n m)

sucℤ+negsuc : ∀ n m → sucℤ (m +negsuc n) ≡ (sucℤ m) +negsuc n
sucℤ+negsuc zero m = (sucPred _) ∙ (sym (predSuc _))
sucℤ+negsuc (suc n) m =      _ ≡⟨ sucPred _ ⟩
  m +negsuc n                    ≡[ i ]⟨ predSuc m (~ i) +negsuc n ⟩
  (predℤ (sucℤ m)) +negsuc n ≡⟨ sym (predℤ+negsuc n (sucℤ m)) ⟩
  predℤ (sucℤ m +negsuc n) ∎

predℤ+pos : ∀ n m → predℤ (m +pos n) ≡ (predℤ m) +pos n
predℤ+pos zero m = refl
predℤ+pos (suc n) m =     _ ≡⟨ predSuc _ ⟩
  m +pos n                    ≡[ i ]⟨ sucPred m (~ i) +pos n ⟩
  (sucℤ (predℤ m)) +pos n ≡⟨ sym (sucℤ+pos n (predℤ m))⟩
  (predℤ m) +pos (suc n)    ∎

predℤ-pos : ∀ n → predℤ(- (pos n)) ≡ negsuc n
predℤ-pos zero    = refl
predℤ-pos (suc n) = refl


{- not needed (for now)
ℕ-f0-pos : ∀ n → n ℕ-f 0 ≡ pos n
ℕ-f0-pos zero    = refl
ℕ-f0-pos (suc n) = refl

∸≡suc→∸swap≡0 : ∀ m n k → m ∸ n ≡ suc k → n ∸ m ≡ 0
∸≡suc→∸swap≡0 zero zero k p       = refl
∸≡suc→∸swap≡0 zero (suc n) k p    = ⊥.rec (ℕ.znots p)
∸≡suc→∸swap≡0 (suc m) zero k p    = refl
∸≡suc→∸swap≡0 (suc m) (suc n) k p = ∸≡suc→∸swap≡0 m n k p

-}


-- maybe we can find a better name (?)
predℕ-f≡ℕ-fsuc : ∀ m n → predℤ (m ℕ-f n) ≡ m ℕ-f (suc n)
predℕ-f≡ℕ-fsuc zero          zero    = refl
predℕ-f≡ℕ-fsuc zero          (suc n) = refl
predℕ-f≡ℕ-fsuc (suc zero)    zero    = refl
predℕ-f≡ℕ-fsuc (suc (suc m)) zero    = refl
predℕ-f≡ℕ-fsuc (suc m)       (suc n) = predℕ-f≡ℕ-fsuc m n

predℤ+ : ∀ m n → predℤ (m + n) ≡ (predℤ m) + n
predℤ+ (pos zero)    (pos zero)          = refl
predℤ+ (pos zero)    (pos (suc zero))    = refl -- sym(ℕ-f0-pos n)
predℤ+ (pos zero)    (pos (suc (suc n))) = refl -- ↙ 
predℤ+ (pos (suc m)) (pos n)             = refl
predℤ+ (pos zero)    (negsuc n)          = refl
predℤ+ (pos (suc m)) (negsuc n)          = predℕ-f≡ℕ-fsuc m n
predℤ+ (negsuc m)    (pos n)             = predℕ-f≡ℕ-fsuc n (suc m)
predℤ+ (negsuc m)    (negsuc n)          = refl


-- +Comm : ∀ m n → m + n ≡ n + m
-- +Comm (pos m)    (pos n)     = cong pos (ℕ.+-comm m n)
-- +Comm (negsuc m) (pos n)     = refl
-- +Comm (pos m) (negsuc n)     = refl  
-- +Comm (negsuc m) (negsuc n)  = cong (negsuc ∘ suc) (ℕ.+-comm m n)


-- +predℤ : ∀ m n → predℤ (m + n) ≡ m + (predℤ n)
-- +predℤ m n = cong predℤ (+Comm m n)  ∙∙ predℤ+ n m ∙∙ +Comm (predℤ n) m

+predℤ : ∀ m n → predℤ (m + n) ≡ m + (predℤ n)
+predℤ (pos zero)          (pos zero)    = refl
+predℤ (pos (suc zero))    (pos zero)    = refl
+predℤ (pos (suc (suc m))) (pos zero)    = cong (pos ∘ suc) (ℕ.+-zero m)
+predℤ (pos m)             (pos (suc n)) = cong (predℤ ∘ pos) (ℕ.+-comm m (suc n)) ∙ cong pos (ℕ.+-comm n m)
+predℤ (pos m)             (negsuc n)    = predℕ-f≡ℕ-fsuc m (suc n)
+predℤ (negsuc m)          (pos zero)    = cong (negsuc ∘ suc) (sym (ℕ.+-zero m))
+predℤ (negsuc m)          (pos (suc n)) = predℕ-f≡ℕ-fsuc n m
+predℤ (negsuc m)          (negsuc n)    = cong (negsuc ∘ suc ∘ suc ) (ℕ.+-comm m n)
                                         ∙ cong (negsuc ∘ suc) (ℕ.+-comm (suc n) m)

sucℕ-fsuc≡ℕ-f : ∀ m n → sucℤ (m ℕ-f suc n) ≡ m ℕ-f n
sucℕ-fsuc≡ℕ-f zero          zero    = refl
sucℕ-fsuc≡ℕ-f zero          (suc n) = refl
sucℕ-fsuc≡ℕ-f (suc zero)    zero    = refl
sucℕ-fsuc≡ℕ-f (suc (suc m)) zero    = refl
sucℕ-fsuc≡ℕ-f (suc m)       (suc n) = sucℕ-fsuc≡ℕ-f m n

sucℤ+ : ∀ m n → sucℤ (m + n) ≡ (sucℤ m) + n
sucℤ+ (pos m)          (pos n)             = refl
sucℤ+ (pos m)          (negsuc n)          = sucℕ-fsuc≡ℕ-f m n
sucℤ+ (negsuc zero)    (pos zero)          = refl
sucℤ+ (negsuc zero)    (pos (suc zero))    = refl
sucℤ+ (negsuc zero)    (pos (suc (suc n))) = refl
sucℤ+ (negsuc (suc m)) (pos n)             = sucℕ-fsuc≡ℕ-f n (suc m)
sucℤ+ (negsuc zero)    (negsuc n)          = refl
sucℤ+ (negsuc (suc m)) (negsuc n)          = refl

+sucℤ : ∀ m n → sucℤ (m + n) ≡ m + (sucℤ n)
+sucℤ (pos m)             (pos n)          = cong (pos ∘ suc) (ℕ.+-comm m n) ∙ cong pos (ℕ.+-comm (suc n) m)
+sucℤ (pos zero)          (negsuc zero)    = refl
+sucℤ (pos (suc zero))    (negsuc zero)    = refl
+sucℤ (pos (suc (suc m))) (negsuc zero)    = cong (pos ∘ suc) (sym (ℕ.+-zero (suc m)))
+sucℤ (pos m)             (negsuc (suc n)) = sucℕ-fsuc≡ℕ-f m (suc n)
+sucℤ (negsuc m)          (pos n)          = sucℕ-fsuc≡ℕ-f n m
+sucℤ (negsuc m)          (negsuc zero)    = cong negsuc (ℕ.+-zero m)
+sucℤ (negsuc m)          (negsuc (suc n)) = cong negsuc (ℕ.+-comm m (suc n) ∙ cong suc (ℕ.+-comm n m))

pos0+ : ∀ z → z ≡ pos 0 + z
pos0+ (pos n)    = refl
pos0+ (negsuc n) = refl

+pos0 : ∀ z → z ≡ z + pos 0
+pos0 (pos n)    = cong pos $ sym (ℕ.+-zero n)
+pos0 (negsuc n) = refl


negsuc0+ : ∀ z → predℤ z ≡ negsuc 0 + z
negsuc0+ (pos zero)          = refl
negsuc0+ (pos (suc zero))    = refl
negsuc0+ (pos (suc (suc n))) = refl
negsuc0+ (negsuc n)          = refl

+negsuc0 : ∀ z → predℤ z ≡ z + negsuc 0
+negsuc0 (pos zero)          = refl
+negsuc0 (pos (suc zero))    = refl
+negsuc0 (pos (suc (suc n))) = refl
+negsuc0 (negsuc n)          = cong (negsuc ∘ suc) $ sym (ℕ.+-zero n) 

ind-comm : {A : Type₀} (_∙_ : A → A → A) (f : ℕ → A) (g : A → A)
           (p : ∀ {n} → f (suc n) ≡ g (f n))
           (g∙ : ∀ a b → g (a ∙ b) ≡ g a ∙ b)
           (∙g : ∀ a b → g (a ∙ b) ≡ a ∙ g b)
           (base : ∀ z → z ∙ f 0 ≡ f 0 ∙ z)
         → ∀ z n → z ∙ f n ≡ f n ∙ z
ind-comm _∙_ f g p g∙ ∙g base z 0 = base z
ind-comm _∙_ f g p g∙ ∙g base z (suc n) =
  z ∙ f (suc n) ≡[ i ]⟨ z ∙ p {n} i ⟩
  z ∙ g (f n)   ≡⟨ sym ( ∙g z (f n)) ⟩
  g (z ∙ f n)   ≡⟨ cong g IH ⟩
  g (f n ∙ z)   ≡⟨ g∙ (f n) z ⟩
  g (f n) ∙ z   ≡[ i ]⟨ p {n} (~ i) ∙ z ⟩
  f (suc n) ∙ z ∎
  where
  IH = ind-comm _∙_ f g p g∙ ∙g base z n

ind-assoc : {A : Type₀} (_·_ : A → A → A) (f : ℕ → A)
        (g : A → A) (p : ∀ a b → g (a · b) ≡ a · (g b))
        (q : ∀ {c} → f (suc c) ≡ g (f c))
        (base : ∀ m n → (m · n) · (f 0) ≡ m · (n · (f 0)))
        (m n : A) (o : ℕ)
      → m · (n · (f o)) ≡ (m · n) · (f o)
ind-assoc _·_ f g p q base m n 0 = sym (base m n)
ind-assoc _·_ f g p q base m n (suc o) =
    m · (n · (f (suc o))) ≡[ i ]⟨ m · (n · q {o} i) ⟩
    m · (n · (g (f o)))   ≡[ i ]⟨ m · (p n (f o) (~ i)) ⟩
    m · (g (n · (f o)))   ≡⟨ sym (p m (n · (f o)))⟩
    g (m · (n · (f o)))   ≡⟨ cong g IH ⟩
    g ((m · n) · (f o))   ≡⟨ p (m · n) (f o) ⟩
    (m · n) · (g (f o))   ≡[ i ]⟨ (m · n) · q {o} (~ i) ⟩
    (m · n) · (f (suc o)) ∎
    where
    IH = ind-assoc _·_ f g p q base m n o

+Comm : ∀ m n → m + n ≡ n + m
+Comm (pos m)    (pos n)     = cong pos (ℕ.+-comm m n)
+Comm (negsuc m) (pos n)     = refl
+Comm (pos m)    (negsuc n)  = refl  
+Comm (negsuc m) (negsuc n)  = cong (negsuc ∘ suc) (ℕ.+-comm m n)

+Comm' : ∀ m n → m + n ≡ n + m
+Comm' m (pos n)    = ind-comm _+_ pos    sucℤ  refl sucℤ+  +sucℤ (λ n → sym (+pos0 n) ∙ pos0+ n) m n
+Comm' m (negsuc n) = ind-comm _+_ negsuc predℤ refl predℤ+ +predℤ (λ n → sym (+negsuc0 n) ∙ negsuc0+ n) m n

+Assoc' : ∀ m n o → m + (n + o) ≡ (m + n) + o
+Assoc' m n (pos o)    = ind-assoc _+_ pos    sucℤ  +sucℤ  refl (λ m n → sym (+pos0 (m + n)) ∙ cong (m +_) (+pos0 n) ) m n o
+Assoc' m n (negsuc o) = ind-assoc _+_ negsuc predℤ +predℤ refl (λ m n → sym (+negsuc0 (m + n))
                                                                      ∙∙ +predℤ m n
                                                                      ∙∙ cong (m +_) (+negsuc0 n) ) m n o
nℕ-fn≡0 : ∀ n → n ℕ-f n ≡ pos 0
nℕ-fn≡0 zero    = refl
nℕ-fn≡0 (suc n) = nℕ-fn≡0 n

ℕ-fSwap : ∀ m n → m ℕ-f n ≡ -(n ℕ-f m)
ℕ-fSwap zero    zero    = refl
ℕ-fSwap zero    (suc n) = refl
ℕ-fSwap (suc m) zero    = refl
ℕ-fSwap (suc m) (suc n) = ℕ-fSwap m n


+PosDistLℕ-f : ∀ m n k → (n ℕ-f k) + (pos m) ≡ (n ℕ.+ m) ℕ-f k
+PosDistLℕ-f zero    zero    zero    = refl
+PosDistLℕ-f (suc m) zero    zero    = refl
+PosDistLℕ-f m       zero    (suc k) = refl
+PosDistLℕ-f m       (suc n) zero    = refl
+PosDistLℕ-f m       (suc n) (suc k) = +PosDistLℕ-f m n k

+PosDistRℕ-f : ∀ m n k → (pos m) + (n ℕ-f k) ≡ (m ℕ.+ n) ℕ-f k
+PosDistRℕ-f m n k = +Comm (pos m) (n ℕ-f k)
                  ∙∙ +PosDistLℕ-f m n k
                  ∙∙ cong (_ℕ-f k) (ℕ.+-comm n m)

+NegsucDistLℕ-f : ∀ m n k → (n ℕ-f k) + negsuc m ≡ n ℕ-f (suc k ℕ.+ m)
+NegsucDistLℕ-f m zero zero       = refl  
+NegsucDistLℕ-f m zero (suc k)    = refl
+NegsucDistLℕ-f m (suc n) zero    = refl
+NegsucDistLℕ-f m (suc n) (suc k) = +NegsucDistLℕ-f m n k

+NegsucDistRℕ-f : ∀ m n k → negsuc m + (n ℕ-f k) ≡ n ℕ-f (suc m ℕ.+ k)
+NegsucDistRℕ-f m n k = +Comm (negsuc m) (n ℕ-f k)
                     ∙∙ +NegsucDistLℕ-f m n k
                     ∙∙ cong (n ℕ-f_ ∘ suc) (ℕ.+-comm k m)

+Assoc : ∀ m n k → m + (n + k) ≡ (m + n) + k
+Assoc (pos m)    (pos n)    (pos k)    = cong pos (ℕ.+-assoc m n k)
+Assoc (pos m)    (pos n)    (negsuc k) = +PosDistRℕ-f m n (suc k)
+Assoc (pos m)    (negsuc n) (pos k)    =
  pos m + k ℕ-f suc n ≡⟨ +PosDistRℕ-f m k (suc n) ⟩
  (m +ℕ k) ℕ-f suc n  ≡⟨ sym (+PosDistLℕ-f k m (suc n)) ⟩
  m ℕ-f suc n + pos k ∎ 
+Assoc (pos m)    (negsuc n) (negsuc k) = sym $ +NegsucDistLℕ-f k m (suc n)
+Assoc (negsuc m) (pos n)    (pos k)    = sym $ +PosDistLℕ-f k n (suc m)
+Assoc (negsuc m) (pos n)    (negsuc k) =
  negsuc m + n ℕ-f suc k   ≡⟨ +NegsucDistRℕ-f m n (suc k) ⟩
  n ℕ-f (suc m +ℕ suc k)   ≡⟨ cong (n ℕ-f_ ∘ suc) (ℕ.+-suc m k) ⟩
  n ℕ-f (suc (suc m) +ℕ k) ≡⟨ sym $ +NegsucDistLℕ-f k n (suc m) ⟩
  n ℕ-f suc m + negsuc k   ∎
+Assoc (negsuc m) (negsuc n) (pos k)    = +NegsucDistRℕ-f m k (suc n) ∙ cong (k ℕ-f_ ∘ suc) (ℕ.+-suc m n)
+Assoc (negsuc m) (negsuc n) (negsuc k) = cong (negsuc ∘ suc) $
  m +ℕ suc (n +ℕ k)   ≡⟨ ℕ.+-suc m (n +ℕ k) ⟩
  suc (m +ℕ (n +ℕ k)) ≡⟨ cong suc (ℕ.+-assoc m n k)  ⟩
  suc (m +ℕ n +ℕ k)   ∎
