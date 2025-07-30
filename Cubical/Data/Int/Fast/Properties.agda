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
open import Cubical.Data.Nat as ℕ hiding (
    +-assoc ; +-comm ; min ; max ; minComm ; maxComm ; minIdem ; maxIdem
  ; minSucL ; minSucR ; maxSucL ; maxSucR)
  renaming (_·_ to _·ℕ_; _+_ to _+ℕ_)
open import Cubical.Data.Sum
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties

open import Cubical.Data.Int.Base as ℤ
  hiding (_+_ ; _·_ ; _-_ ; _ℕ-_ ; sumFinℤ ; sumFinℤId)
open import Cubical.Data.Int.Properties as P public using (
    injPos ; injNegsuc ; posNotnegsuc ; negsucNotpos ; injNeg ; discreteℤ ; isSetℤ
  ; -pos ; -neg ; sucℤnegsucneg ; -sucℤ ; -predℤ ; -Involutive ; isEquiv-
  ; predℤ+negsuc ; sucℤ+negsuc ; predℤ-pos ; ind-assoc ; ind-comm
  ; sucPathℤ ; addEq ; predPathℤ ; subEq ; _+'_ ; isEquivAddℤ'
  ; abs→⊎ ; ⊎→abs ; abs≡0 ; ¬x≡0→¬abs≡0 ; abs- ; 0≢1-ℤ)

open import Cubical.Data.Int.Fast.Base

private
  ℕ-lem : ∀ n m → (pos n +negsuc m) ≡ (n ℕ- suc m)
  ℕ-lem zero          zero    = refl
  ℕ-lem (suc zero)    zero    = refl
  ℕ-lem (suc (suc n)) zero    = refl
  ℕ-lem zero          (suc m) = cong predℤ (P.+Comm 0 (negsuc m))
  ℕ-lem (suc n)       (suc m) = predℤ+negsuc m (pos (suc n)) ∙ ℕ-lem n m

+≡+f : ∀ n m → n ℤ.+ m ≡ n + m
+≡+f (pos n)    (pos n₁)    = sym (P.pos+ n n₁)
+≡+f (pos n)    (negsuc n₁) = ℕ-lem n n₁
+≡+f (negsuc n) (pos n₁)    = P.+Comm (negsuc n) (pos n₁) ∙ ℕ-lem n₁ n
+≡+f (negsuc n) (negsuc n₁) = sym (P.neg+ (suc n) (suc n₁))
                            ∙ cong negsuc (ℕ.+-suc _ _)

·≡·f : ∀ n m → n ℤ.· m ≡ n · m
·≡·f (pos n)       (pos n₁)       = sym (P.pos·pos n n₁)
·≡·f (pos zero)    (negsuc n₁)    = refl
·≡·f (pos (suc n)) (negsuc n₁)    = P.pos·negsuc (suc n) n₁
                                  ∙ cong -_ (sym (P.pos·pos (suc n) (suc n₁)))
·≡·f (negsuc n)    (pos zero)     = P.·AnnihilR (negsuc n)
·≡·f (negsuc n)    (pos (suc n₁)) = P.negsuc·pos n (suc n₁)
                                  ∙ cong -_ (sym (P.pos·pos (suc n) (suc n₁)))
·≡·f (negsuc n)    (negsuc n₁)    = P.negsuc·negsuc n n₁
                                  ∙ sym (P.pos·pos (suc n) (suc n₁))

subst-f : (A : (ℤ → ℤ → ℤ) → (ℤ → ℤ → ℤ) → Type) → A ℤ._+_ ℤ._·_ → A _+_ _·_
subst-f A = subst2 A (λ i x y → +≡+f x y i) (λ i x y → ·≡·f x y i)

·DistPosRMin : (x : ℕ) (y z : ℤ) → pos x · P.min y z ≡ P.min (pos x · y) (pos x · z)
·DistPosRMin x y z = subst-f
  (λ _+_ _·_ → pos x · P.min y z ≡ P.min (pos x · y) (pos x · z)) (P.·DistPosRMin x y z)

sucℤ[negsuc]-pos : ∀ k → sucℤ (negsuc k) ≡ - pos k
sucℤ[negsuc]-pos zero    = refl
sucℤ[negsuc]-pos (suc k) = refl

+IdL : ∀ z → 0 + z ≡ z
+IdL (pos n)    = refl
+IdL (negsuc n) = refl

+IdR : ∀ z → z + 0 ≡ z
+IdR (pos n)    = cong pos (+-zero n)
+IdR (negsuc n) = refl

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

minIdem : ∀ n → min n n ≡ n
minIdem (pos n)    = cong pos (ℕ.minIdem n)
minIdem (negsuc n) = cong negsuc (ℕ.maxIdem n)

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
maxIdem (pos n)    = cong pos (ℕ.maxIdem n)
maxIdem (negsuc n) = cong negsuc (ℕ.minIdem n)

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

minSucL : ∀ m → min (sucℤ m) m ≡ m
minSucL (pos m)          = cong pos (ℕ.minSucL m)
minSucL (negsuc zero)    = refl
minSucL (negsuc (suc m)) = cong negsuc (ℕ.maxSucR m)

minSucR : ∀ m → min m (sucℤ m)  ≡ m
minSucR m = minComm m (sucℤ m) ∙ minSucL m

minPredL : ∀ m → min (predℤ m) m ≡ predℤ m
minPredL (pos zero)    = refl
minPredL (pos (suc m)) = cong pos (ℕ.minSucR m)
minPredL (negsuc m)    = cong negsuc (ℕ.maxSucL m)

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
maxSucL (pos m)          = cong pos (ℕ.maxSucL m)
maxSucL (negsuc zero)    = refl
maxSucL (negsuc (suc m)) = cong negsuc (ℕ.minSucR m)

maxSucR : ∀ m → max m (sucℤ m) ≡ sucℤ m
maxSucR m = maxComm m (sucℤ m) ∙ maxSucL m

maxPredL : ∀ m → max (predℤ m) m ≡ m
maxPredL (pos zero)    = refl
maxPredL (pos (suc m)) = cong pos (ℕ.maxSucR m)
maxPredL (negsuc m)    = cong negsuc (ℕ.minSucL m)

maxPredR : ∀ m → max m (predℤ m) ≡ m
maxPredR m = maxComm m (predℤ m) ∙ maxPredL m

predℤ+pos : ∀ n m → predℤ (m +pos n) ≡ (predℤ m) +pos n
predℤ+pos zero m = refl
predℤ+pos (suc n) m =
  predℤ (sucℤ (m +pos n))   ≡⟨ predSuc _ ⟩
  m +pos n                  ≡[ i ]⟨ sucPred m (~ i) +pos n ⟩
  (sucℤ (predℤ m)) +pos n   ≡⟨ sym (P.sucℤ+pos n (predℤ m))⟩
  (predℤ m) +pos (suc n)    ∎

-- maybe we can find a better name (?)
predℕ-≡ℕ-suc : ∀ m n → predℤ (m ℕ- n) ≡ m ℕ- (suc n)
predℕ-≡ℕ-suc zero          zero    = refl
predℕ-≡ℕ-suc zero          (suc n) = refl
predℕ-≡ℕ-suc (suc zero)    zero    = refl
predℕ-≡ℕ-suc (suc (suc m)) zero    = refl
predℕ-≡ℕ-suc (suc m)       (suc n) = predℕ-≡ℕ-suc m n

predℤ+ : ∀ m n → predℤ (m + n) ≡ (predℤ m) + n
predℤ+ (pos zero)    (pos zero)          = refl
predℤ+ (pos zero)    (pos (suc zero))    = refl
predℤ+ (pos zero)    (pos (suc (suc n))) = refl
predℤ+ (pos (suc m)) (pos n)             = refl
predℤ+ (pos zero)    (negsuc n)          = refl
predℤ+ (pos (suc m)) (negsuc n)          = predℕ-≡ℕ-suc m n
predℤ+ (negsuc m)    (pos n)             = predℕ-≡ℕ-suc n (suc m)
predℤ+ (negsuc m)    (negsuc n)          = refl

+predℤ : ∀ m n → predℤ (m + n) ≡ m + (predℤ n)
+predℤ (pos zero)          (pos zero)    = refl
+predℤ (pos (suc zero))    (pos zero)    = refl
+predℤ (pos (suc (suc m))) (pos zero)    = cong (pos ∘ suc) (ℕ.+-zero m)
+predℤ (pos m)             (pos (suc n)) = cong (predℤ ∘ pos) (ℕ.+-comm m (suc n)) ∙ cong pos (ℕ.+-comm n m)
+predℤ (pos m)             (negsuc n)    = predℕ-≡ℕ-suc m (suc n)
+predℤ (negsuc m)          (pos zero)    = cong (negsuc ∘ suc) (sym (ℕ.+-zero m))
+predℤ (negsuc m)          (pos (suc n)) = predℕ-≡ℕ-suc n m
+predℤ (negsuc m)          (negsuc n)    = cong (negsuc ∘ suc ∘ suc ) (ℕ.+-comm m n)
                                         ∙ cong (negsuc ∘ suc) (ℕ.+-comm (suc n) m)

sucℕ-suc≡ℕ- : ∀ m n → sucℤ (m ℕ- suc n) ≡ m ℕ- n
sucℕ-suc≡ℕ- zero          zero    = refl
sucℕ-suc≡ℕ- zero          (suc n) = refl
sucℕ-suc≡ℕ- (suc zero)    zero    = refl
sucℕ-suc≡ℕ- (suc (suc m)) zero    = refl
sucℕ-suc≡ℕ- (suc m)       (suc n) = sucℕ-suc≡ℕ- m n

sucℤ+pos : ∀ n m → sucℤ (m + pos n) ≡ (sucℤ m) + pos n
sucℤ+pos n (pos n₁)                  = refl
sucℤ+pos zero (negsuc n₁)            = sym (+IdR (sucℤ (negsuc n₁ + pos zero)))
sucℤ+pos (suc zero) (negsuc zero)    = refl
sucℤ+pos (suc (suc n)) (negsuc zero) = cong (sucℤ ∘ (ℕ-hlp (suc n))) (zero∸ (suc n))
sucℤ+pos (suc n) (negsuc (suc n₁))   = w n n₁ where
  w : ∀ n m → sucℤ (ℕ-hlp (n ∸ suc m) (suc m ∸ n)) ≡ ℕ-hlp (n ∸ m) (m ∸ n)
  w zero zero          = refl
  w zero (suc m)       = refl
  w (suc zero) zero    = refl
  w (suc (suc n)) zero = cong (sucℤ ∘ (ℕ-hlp (suc n))) (zero∸ (suc n))
  w (suc n) (suc m)    = w n m

sucℤ+ : ∀ m n → sucℤ (m + n) ≡ (sucℤ m) + n
sucℤ+ (pos m)          (pos n)             = refl
sucℤ+ (pos m)          (negsuc n)          = sucℕ-suc≡ℕ- m n
sucℤ+ (negsuc zero)    (pos zero)          = refl
sucℤ+ (negsuc zero)    (pos (suc zero))    = refl
sucℤ+ (negsuc zero)    (pos (suc (suc n))) = refl
sucℤ+ (negsuc (suc m)) (pos n)             = sucℕ-suc≡ℕ- n (suc m)
sucℤ+ (negsuc zero)    (negsuc n)          = refl
sucℤ+ (negsuc (suc m)) (negsuc n)          = refl

+sucℤ : ∀ m n → sucℤ (m + n) ≡ m + (sucℤ n)
+sucℤ (pos m)             (pos n)          = cong (pos ∘ suc) (ℕ.+-comm m n) ∙ cong pos (ℕ.+-comm (suc n) m)
+sucℤ (pos zero)          (negsuc zero)    = refl
+sucℤ (pos (suc zero))    (negsuc zero)    = refl
+sucℤ (pos (suc (suc m))) (negsuc zero)    = cong (pos ∘ suc) (sym (ℕ.+-zero (suc m)))
+sucℤ (pos m)             (negsuc (suc n)) = sucℕ-suc≡ℕ- m (suc n)
+sucℤ (negsuc m)          (pos n)          = sucℕ-suc≡ℕ- n m
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

nℕ-n≡0 : ∀ n → n ℕ- n ≡ pos 0
nℕ-n≡0 zero    = refl
nℕ-n≡0 (suc n) = nℕ-n≡0 n

+PosDistLℕ- : ∀ m n k → (n ℕ- k) + (pos m) ≡ (n ℕ.+ m) ℕ- k
+PosDistLℕ- zero    zero    zero    = refl
+PosDistLℕ- (suc m) zero    zero    = refl
+PosDistLℕ- m       zero    (suc k) = refl
+PosDistLℕ- m       (suc n) zero    = refl
+PosDistLℕ- m       (suc n) (suc k) = +PosDistLℕ- m n k

+PosDistRℕ- : ∀ m n k → (pos m) + (n ℕ- k) ≡ (m ℕ.+ n) ℕ- k
+PosDistRℕ- m n k = +Comm (pos m) (n ℕ- k)
                 ∙∙ +PosDistLℕ- m n k
                 ∙∙ cong (_ℕ- k) (ℕ.+-comm n m)

+NegsucDistLℕ- : ∀ m n k → (n ℕ- k) + negsuc m ≡ n ℕ- (suc k ℕ.+ m)
+NegsucDistLℕ- m zero zero       = refl
+NegsucDistLℕ- m zero (suc k)    = refl
+NegsucDistLℕ- m (suc n) zero    = refl
+NegsucDistLℕ- m (suc n) (suc k) = +NegsucDistLℕ- m n k

+NegsucDistRℕ- : ∀ m n k → negsuc m + (n ℕ- k) ≡ n ℕ- (suc m ℕ.+ k)
+NegsucDistRℕ- m n k = +Comm (negsuc m) (n ℕ- k)
                    ∙∙ +NegsucDistLℕ- m n k
                    ∙∙ cong (n ℕ-_ ∘ suc) (ℕ.+-comm k m)

+Assoc : ∀ m n k → m + (n + k) ≡ (m + n) + k
+Assoc (pos m)    (pos n)    (pos k)    = cong pos (ℕ.+-assoc m n k)
+Assoc (pos m)    (pos n)    (negsuc k) = +PosDistRℕ- m n (suc k)
+Assoc (pos m)    (negsuc n) (pos k)    =
  pos m + k ℕ- suc n ≡⟨ +PosDistRℕ- m k (suc n) ⟩
  (m +ℕ k) ℕ- suc n  ≡⟨ sym (+PosDistLℕ- k m (suc n)) ⟩
  m ℕ- suc n + pos k ∎
+Assoc (pos m)    (negsuc n) (negsuc k) = sym $ +NegsucDistLℕ- k m (suc n)
+Assoc (negsuc m) (pos n)    (pos k)    = sym $ +PosDistLℕ- k n (suc m)
+Assoc (negsuc m) (pos n)    (negsuc k) =
  negsuc m + n ℕ- suc k   ≡⟨ +NegsucDistRℕ- m n (suc k) ⟩
  n ℕ- (suc m +ℕ suc k)   ≡⟨ cong (n ℕ-_ ∘ suc) (ℕ.+-suc m k) ⟩
  n ℕ- (suc (suc m) +ℕ k) ≡⟨ sym $ +NegsucDistLℕ- k n (suc m) ⟩
  n ℕ- suc m + negsuc k   ∎
+Assoc (negsuc m) (negsuc n) (pos k)    = +NegsucDistRℕ- m k (suc n) ∙ cong (k ℕ-_ ∘ suc) (ℕ.+-suc m n)
+Assoc (negsuc m) (negsuc n) (negsuc k) = cong (negsuc ∘ suc) $
  m +ℕ suc (n +ℕ k)   ≡⟨ ℕ.+-suc m (n +ℕ k) ⟩
  suc (m +ℕ (n +ℕ k)) ≡⟨ cong suc (ℕ.+-assoc m n k)  ⟩
  suc (m +ℕ n +ℕ k)   ∎

+'≡+ : _+'_ ≡ _+_
+'≡+ =  P.+'≡+ ∙ (λ i x y → +≡+f x y i)

isEquivAddℤ : (m : ℤ) → isEquiv (λ n → n + m)
isEquivAddℤ = subst (λ add → (m : ℤ) → isEquiv (λ n → add n m)) +'≡+ P.isEquivAddℤ'

-- below is an alternate proof of isEquivAddℤ for comparison
-- We also have two useful lemma here.

-Cancel : ∀ z → z - z ≡ 0
-Cancel (pos zero) = refl
-Cancel (pos (suc n)) = nℕ-n≡0 n
-Cancel (negsuc n) = nℕ-n≡0 n

-Cancel' : ∀ z → - z + z ≡ 0
-Cancel' z = +Comm (- z) z ∙ -Cancel z

minusPlus : ∀ m n → (n - m) + m ≡ n
minusPlus m n = (sym (+Assoc n (- m) m))
             ∙∙ cong (n +_) (-Cancel' m)
             ∙∙ sym (+pos0 n)

plusMinus : ∀ m n → (n + m) - m ≡ n
plusMinus m n = sym (+Assoc n m (- m))
             ∙∙ cong (n +_) (-Cancel m)
             ∙∙ sym (+pos0 n)

private
  alternateProof : (m : ℤ) → isEquiv (λ n → n + m)
  alternateProof m = isoToIsEquiv (iso (λ n → n + m)
                                       (λ n → n - m)
                                       (minusPlus m)
                                       (plusMinus m))

-≡0 : (m n : ℤ) → m - n ≡ 0 → m ≡ n
-≡0 m n p =
  m         ≡⟨ sym (minusPlus n m) ⟩
  m - n + n ≡⟨ cong (_+ n) p  ⟩
  pos 0 + n ≡⟨ sym (pos0+ n) ⟩
  n         ∎

pos+ : ∀ m n → pos (m +ℕ n) ≡ pos m + pos n
pos+ m n = refl

negsuc+ : ∀ m n → negsuc (m +ℕ n) ≡ negsuc m - pos n
negsuc+ m zero    = cong negsuc (ℕ.+-zero m)
negsuc+ m (suc n) = cong negsuc (ℕ.+-suc m n)

neg+ : ∀ m n → neg (m +ℕ n) ≡ neg m + neg n
neg+ zero    zero    = refl
neg+ zero    (suc n) = refl
neg+ (suc m) zero    = cong negsuc (ℕ.+-zero m)
neg+ (suc m) (suc n) = cong negsuc (ℕ.+-suc m n)

ℕ-AntiComm : ∀ m n → m ℕ- n ≡ -(n ℕ- m)
ℕ-AntiComm zero    zero    = refl
ℕ-AntiComm zero    (suc n) = refl
ℕ-AntiComm (suc m) zero    = refl
ℕ-AntiComm (suc m) (suc n) = ℕ-AntiComm m n

pos- : ∀ m n → m ℕ- n ≡ pos m - pos n
pos- zero    zero    = refl
pos- (suc m) zero    = cong (pos ∘ suc) (sym (ℕ.+-zero m))
pos- m       (suc n) = refl

-AntiComm : ∀ m n → m - n ≡ - (n - m)
-AntiComm (pos m)       (pos n)       = sym (pos- m n) ∙∙ ℕ-AntiComm m n ∙∙ cong -_ (pos- n m)
-AntiComm (pos zero)    (negsuc n)    = refl
-AntiComm (pos (suc m)) (negsuc n)    = cong (pos ∘ suc) (ℕ.+-comm m (suc n))
-AntiComm (negsuc m)    (pos zero)    = refl
-AntiComm (negsuc m)    (pos (suc n)) = cong negsuc (ℕ.+-comm (suc m) n)
-AntiComm (negsuc m)    (negsuc n)    = ℕ-AntiComm n m

-Dist+ : ∀ m n → - (m + n) ≡ (- m) + (- n)
-Dist+ (pos zero)    (pos zero)    = refl
-Dist+ (pos zero)    (pos (suc n)) = refl
-Dist+ (pos (suc m)) (pos zero)    = cong negsuc (ℕ.+-zero m)
-Dist+ (pos (suc m)) (pos (suc n)) = cong negsuc (ℕ.+-suc m n)
-Dist+ (pos zero)    (negsuc n)    = refl
-Dist+ (pos (suc m)) (negsuc n)    = sym (ℕ-AntiComm n m)
-Dist+ (negsuc m)    (pos zero)    = cong (pos ∘ suc) $ sym $ ℕ.+-zero m
-Dist+ (negsuc m)    (pos (suc n)) = sym (ℕ-AntiComm m n)
-Dist+ (negsuc m)    (negsuc n)    = cong (pos ∘ suc) $ sym $ ℕ.+-suc m n

inj-z+ : ∀ {z l n} → z + l ≡ z + n → l ≡ n
inj-z+ {z} {l} {n} p =
  l             ≡⟨ pos0+ l ⟩
  0 + l         ≡⟨ cong (_+ l) (sym (-Cancel' z)) ⟩
  - z + z + l   ≡⟨ sym (+Assoc (- z) z l)  ⟩
  - z + (z + l) ≡⟨ cong (- z +_) p ⟩
  - z + (z + n) ≡⟨ +Assoc (- z) z n ⟩
  - z + z + n   ≡⟨ cong (_+ n) (-Cancel' z) ⟩
  0 + n         ≡⟨ sym (pos0+ n) ⟩
  n             ∎

inj-+z : ∀ {z l n} → l + z ≡ n + z → l ≡ n
inj-+z {z} {l} {n} p = inj-z+ {z = z} {l} {n} (+Comm z l ∙∙ p ∙∙ +Comm n z)

n+z≡z→n≡0 : ∀ n z → n + z ≡ z → n ≡ 0
n+z≡z→n≡0 n z p = inj-z+ {z = z} {l = n} {n = 0} (+Comm z n ∙∙ p ∙∙ +pos0 z)

pos·pos : (n m : ℕ) → pos (n ·ℕ m) ≡ pos n · pos m
pos·pos n m = refl

pos·negsuc : (n m : ℕ) → pos n · negsuc m ≡ - (pos n · pos (suc m))
pos·negsuc zero    m = refl
pos·negsuc (suc n) m = refl

negsuc·pos : (n m : ℕ) → negsuc n · pos m ≡ - (pos (suc n) · pos m)
negsuc·pos n zero    = cong (-_ ∘ pos) (ℕ.0≡m·0 n)
negsuc·pos n (suc m) = refl

negsuc·negsuc : (n m : ℕ) → negsuc n · negsuc m ≡ pos (suc n) · pos (suc m)
negsuc·negsuc n m = refl

negsuc·ℤ : (n : ℕ) → (m : ℤ) → negsuc n · m ≡ - (pos (suc n) · m)
negsuc·ℤ n (pos m)    = negsuc·pos n m
negsuc·ℤ n (negsuc m) = refl

·Comm : (x y : ℤ) → x · y ≡ y · x
·Comm (pos m)       (pos n)       = cong pos (ℕ.·-comm m n)
·Comm (pos zero)    (negsuc n)    = refl
·Comm (pos (suc m)) (negsuc n)    = cong neg $ ℕ.·-comm (suc m) (suc n)
·Comm (negsuc m)    (pos zero)    = refl
·Comm (negsuc m)    (pos (suc n)) = cong neg $ ℕ.·-comm (suc m) (suc n)
·Comm (negsuc m)    (negsuc n)    = cong pos $ ℕ.·-comm (suc m) (suc n)

·IdR : (x : ℤ) → x · 1 ≡ x
·IdR (pos n)    = cong pos (ℕ.·-identityʳ n)
·IdR (negsuc n) = cong negsuc (ℕ.·-identityʳ n)

·IdL : (x : ℤ) → 1 · x ≡ x
·IdL (pos n)    = cong pos (ℕ.+-zero n)
·IdL (negsuc n) = cong negsuc (ℕ.+-zero n)

·AnnihilR : (x : ℤ) → x · 0 ≡ 0
·AnnihilR (pos n)    = cong pos $ sym $ ℕ.0≡m·0 n
·AnnihilR (negsuc n) = refl

·AnnihilL : (x : ℤ) → 0 · x ≡ 0
·AnnihilL (pos n)    = refl
·AnnihilL (negsuc n) = refl

-1·x≡-x : ∀ x → -1 · x ≡ - x
-1·x≡-x (pos zero)    = refl
-1·x≡-x (pos (suc n)) = cong negsuc (+-zero n)
-1·x≡-x (negsuc n)    = cong (pos ∘ suc) (+-zero n)

private
  distrHelper : (x y z w : ℤ) → (x + y) + (z + w) ≡ ((x + z) + (y + w))
  distrHelper x y z w =
      +Assoc (x + y) z w
   ∙∙ cong (_+ w) (sym (+Assoc x y z) ∙∙ cong (x +_) (+Comm y z) ∙∙ +Assoc x z y)
   ∙∙ sym (+Assoc (x + z) y w)

-- maybe we can find a better name (?)
+ℕ- : ∀ m n l → (m +ℕ n) ℕ- (m +ℕ l) ≡ n ℕ- l
+ℕ- zero    n l = refl
+ℕ- (suc m) n l = +ℕ- m n l

Pos·DistRℕ- : ∀ x y z → pos x · y ℕ- z ≡ (x ·ℕ y ) ℕ- (x ·ℕ z)
Pos·DistRℕ- zero y z = ·AnnihilL (y ℕ- z)
Pos·DistRℕ- (suc x) zero zero =
  pos (x ·ℕ zero)            ≡⟨ cong pos $ sym $ ℕ.0≡m·0 x ⟩
  pos 0                      ≡⟨ cong₂ _ℕ-_ (ℕ.0≡m·0 x) (ℕ.0≡m·0 x) ⟩
  (x ·ℕ zero) ℕ- (x ·ℕ zero) ∎
Pos·DistRℕ- (suc x) zero    (suc z) = cong (_ℕ- (suc x ·ℕ suc z)) (ℕ.0≡m·0 x)
Pos·DistRℕ- (suc x) (suc y) zero    = cong ((suc x ·ℕ suc y) ℕ-_) (ℕ.0≡m·0 x)
Pos·DistRℕ- (suc x) (suc y) (suc z) =
  pos (suc x) · (y ℕ- z)                         ≡⟨ Pos·DistRℕ- (suc x) y z ⟩
  (suc x ·ℕ y) ℕ- (suc x ·ℕ z)                   ≡⟨ sym $ +ℕ- (suc x) (suc x ·ℕ y) (suc x ·ℕ z) ⟩
  (suc x +ℕ suc x ·ℕ y) ℕ- (suc x +ℕ suc x ·ℕ z) ≡⟨ sym $ cong₂ _ℕ-_ (ℕ.·-suc (suc x) y) (ℕ.·-suc (suc x) z) ⟩
  (suc x ·ℕ suc y) ℕ- (suc x ·ℕ suc z)           ∎

Negsuc·DistRℕ- : ∀ x y z → negsuc x · y ℕ- z ≡ (suc x ·ℕ suc z) ℕ- (suc x ·ℕ suc y)
Negsuc·DistRℕ- m n l =
  negsuc m · (suc n ℕ- suc l)                  ≡⟨ negsuc·ℤ m (n ℕ- l) ⟩
  - (pos (suc m) · (suc n ℕ- suc l))           ≡⟨ cong -_ (Pos·DistRℕ- (suc m) (suc n) (suc l)) ⟩
  - ((suc m ·ℕ suc n) ℕ- (suc m ·ℕ suc l))     ≡⟨ sym $ ℕ-AntiComm (suc m ·ℕ suc l) (suc m ·ℕ suc n) ⟩
  negsuc m · pos (suc n) + negsuc m · negsuc l ∎

·DistR+ : (x y z : ℤ) → x · (y + z) ≡ x · y + x · z
·DistR+ (pos m)       (pos n)    (pos l)    = cong pos $ sym $ ℕ.·-distribˡ m n l
·DistR+ (pos zero)    (pos n)    (negsuc l) = ·AnnihilL (n ℕ- suc l)
·DistR+ (pos (suc m)) (pos n)    (negsuc l) = Pos·DistRℕ- (suc m) n (suc l)
·DistR+ (pos zero)    (negsuc n) (pos l)    = ·AnnihilL (l ℕ- suc n)
·DistR+ (pos (suc m)) (negsuc n) (pos l)    = Pos·DistRℕ- (suc m) l (suc n)
·DistR+ (pos zero)    (negsuc n) (negsuc l) = refl
·DistR+ (pos (suc m)) (negsuc n) (negsuc l) = cong neg $
  suc m ·ℕ suc (suc (n +ℕ l))               ≡⟨ cong (suc m ·ℕ_) (sym (ℕ.+-suc (suc n) l)) ⟩
  suc m ·ℕ (suc n +ℕ suc l)                 ≡⟨ sym (ℕ.·-distribˡ (suc m) (suc n) (suc l)) ⟩
  suc m ·ℕ suc n +ℕ suc m ·ℕ suc l          ≡⟨⟩
  suc m ·ℕ suc n +ℕ suc (l +ℕ m ·ℕ suc l)   ≡⟨ ℕ.+-suc (suc m ·ℕ suc n) (l +ℕ m ·ℕ suc l) ⟩
  suc (suc m ·ℕ suc n) +ℕ (l +ℕ m ·ℕ suc l) ∎
·DistR+ (negsuc m) (pos zero)    (pos zero)    = refl
·DistR+ (negsuc m) (pos zero)    (pos (suc l)) = refl
·DistR+ (negsuc m) (pos (suc n)) (pos zero)    = λ i → negsuc $ (ℕ.+-zero n i) +ℕ m ·ℕ suc (ℕ.+-zero n i)
·DistR+ (negsuc m) (pos (suc n)) (pos (suc l)) = cong neg $
  suc m ·ℕ suc (n +ℕ suc l)                      ≡⟨ (sym $ ℕ.·-distribˡ (suc m) (suc n) (suc l) ) ⟩
  suc m ·ℕ suc n +ℕ suc m ·ℕ suc l               ≡⟨⟩
  suc n +ℕ m ·ℕ suc n +ℕ suc (l +ℕ m ·ℕ suc l)   ≡⟨ ℕ.+-suc ((suc n) +ℕ m ·ℕ suc n) (l +ℕ m ·ℕ suc l)  ⟩
  suc (suc n) +ℕ m ·ℕ suc n +ℕ (l +ℕ m ·ℕ suc l) ∎
·DistR+ (negsuc m) (pos zero)    (negsuc l)    = refl
·DistR+ (negsuc m) (pos (suc n)) (negsuc l)    = Negsuc·DistRℕ- m n l
·DistR+ (negsuc m) (negsuc n)    (pos zero)    = cong pos $ sym $ ℕ.+-zero (suc m ·ℕ suc n)
·DistR+ (negsuc m) (negsuc n)    (pos (suc l)) = Negsuc·DistRℕ- m l n
·DistR+ (negsuc m) (negsuc n)    (negsuc l)    = cong pos $
  suc m ·ℕ suc (suc (n +ℕ l))      ≡⟨ cong (suc m ·ℕ_) (sym (ℕ.+-suc (suc n) l)) ⟩
  suc m ·ℕ (suc n +ℕ suc l)        ≡⟨ sym (ℕ.·-distribˡ (suc m) (suc n) (suc l)) ⟩
  suc m ·ℕ suc n +ℕ suc m ·ℕ suc l ∎

·DistL+ : (x y z : ℤ) → (x + y) · z ≡ x · z + y · z
·DistL+ x y z = ·Comm (x + y) z ∙∙ ·DistR+ z x y ∙∙ cong₂ _+_ (·Comm z x) (·Comm z y)

-DistL· : (b c : ℤ) → - (b · c) ≡ - b · c
-DistL· (pos zero)    (pos n)       = refl
-DistL· (pos (suc m)) (pos zero)    = cong (-_ ∘ pos) $ sym $ ℕ.0≡m·0 m
-DistL· (pos (suc m)) (pos (suc n)) = refl
-DistL· (pos zero)    (negsuc n)    = refl
-DistL· (pos (suc m)) (negsuc n)    = refl
-DistL· (negsuc m)    (pos zero)    = cong pos (ℕ.0≡m·0 m)
-DistL· (negsuc m)    (pos (suc n)) = refl
-DistL· (negsuc m)    (negsuc n)    = refl

-DistR· : (b c : ℤ) → - (b · c) ≡ b · - c
-DistR· b c = cong (-_) (·Comm b c) ∙∙ -DistL· c b ∙∙ ·Comm (- c) b

-DistLR· : (b c : ℤ) → b · c ≡ - b · - c
-DistLR· b c = sym (-Involutive (b · c)) ∙ (λ i → - -DistL· b c i) ∙ -DistR· (- b) c

ℤ·negsuc : (n : ℤ) (m : ℕ) → n · negsuc m ≡ - (n · pos (suc m))
ℤ·negsuc (pos zero)    zero    = refl
ℤ·negsuc (pos (suc n)) zero    = refl
ℤ·negsuc (pos zero)    (suc m) = refl
ℤ·negsuc (pos (suc n)) (suc m) = refl
ℤ·negsuc (negsuc n)    zero    = refl
ℤ·negsuc (negsuc n)    (suc m) = refl

private
  neg·Assoc : ∀ m n l → negsuc m · (negsuc n · negsuc l) ≡ (negsuc m · negsuc n) · negsuc l
  neg·Assoc m n l = cong neg (ℕ.·-assoc (suc m) (suc n) (suc l))
  pos·Assoc : ∀ m n l → pos m · (pos n · pos l) ≡ (pos m · pos n) · pos l
  pos·Assoc m n l = cong pos (ℕ.·-assoc m n l)

·Assoc : (a b c : ℤ) → (a · (b · c)) ≡ ((a · b) · c)
·Assoc (pos m)       (pos n)       (pos l)       = pos·Assoc m n l
·Assoc (pos m)       (pos (zero))  (negsuc l)    =
  pos (suc m ·ℕ 0)           ≡⟨ cong pos $ sym $ ℕ.0≡m·0 m ⟩
  0                          ≡⟨ sym $ ·AnnihilL (negsuc l) ⟩
  0 · negsuc l               ≡⟨ cong (_· negsuc l) (cong pos (ℕ.0≡m·0 m)) ⟩
  pos (m ·ℕ zero) · negsuc l ∎
·Assoc (pos zero)    (pos (suc n)) (negsuc l)    = refl
·Assoc (pos (suc m)) (pos (suc n)) (negsuc l)    = neg·Assoc m n l
·Assoc (pos zero)    (negsuc n)    (pos zero)    = refl
·Assoc (pos zero)    (negsuc n)    (pos (suc l)) = refl
·Assoc (pos (suc m)) (negsuc n)    (pos zero)    = cong pos $ sym $ ℕ.0≡m·0 m
·Assoc (pos (suc m)) (negsuc n)    (pos (suc l)) = neg·Assoc m n l
·Assoc (pos zero)    (negsuc n)    (negsuc l)    = refl
·Assoc (pos (suc m)) (negsuc n)    (negsuc l)    = pos·Assoc (suc m) (suc n) (suc l)
·Assoc (negsuc m)    (pos zero)    (pos l)       = refl
·Assoc (negsuc m)    (pos (suc n)) (pos zero)    =
  negsuc m · pos (n ·ℕ 0) ≡⟨ cong ((negsuc m ·_) ∘ pos) $ sym $ ℕ.0≡m·0 n ⟩
  negsuc m · 0            ≡⟨ ·AnnihilR (negsuc m) ⟩
  0                       ∎
·Assoc (negsuc m)    (pos (suc n)) (pos (suc l)) = neg·Assoc m n l
·Assoc (negsuc m)    (pos zero)    (negsuc l)    = refl
·Assoc (negsuc m)    (pos (suc n)) (negsuc l)    = pos·Assoc (suc m) (suc n) (suc l)
·Assoc (negsuc m)    (negsuc n)    (pos zero)    = cong pos $ ℕ.0≡m·0 (suc m ·ℕ suc n)
·Assoc (negsuc m)    (negsuc n)    (pos (suc l)) = pos·Assoc (suc m) (suc n) (suc l)
·Assoc (negsuc m)    (negsuc n)    (negsuc l)    = neg·Assoc m n l

·suc→0 : (a : ℤ) (b : ℕ) → a · pos (suc b) ≡ 0 → a ≡ 0
·suc→0 (pos n) b n·b≡0 = cong pos (sym (0≡n·sm→0≡n (sym (injPos (pos·pos n (suc b) ∙ n·b≡0)))))
·suc→0 (negsuc n) b n·b≡0 = ⊥.rec (snotz
                                     (injNeg
                                      (cong -_ (pos·pos (suc n) (suc b)) ∙
                                       sym (negsuc·pos n (suc b)) ∙
                                       n·b≡0)))

sucℤ≡1+ : ∀ a → sucℤ a ≡ 1 + a
sucℤ≡1+ (pos n)          = refl
sucℤ≡1+ (negsuc zero)    = refl
sucℤ≡1+ (negsuc (suc n)) = refl

sucℤ· : (a b : ℤ) → sucℤ a · b ≡ b + a · b
sucℤ· a b =
  sucℤ a · b    ≡⟨ cong (_· b) (sucℤ≡1+ a) ⟩
  (1 + a) · b   ≡⟨ ·DistL+ 1 a b ⟩
  1 · b + a · b ≡⟨ cong (_+ a · b) (·IdL b) ⟩
  b + a · b     ∎

·sucℤ : (a b : ℤ) → a · sucℤ b ≡ a · b + a
·sucℤ a b = ·Comm a (sucℤ b) ∙ sucℤ· b a ∙ cong (a +_) (·Comm b a) ∙ +Comm a (a · b)

predℤ≡-1 : ∀ a → predℤ a ≡ a - 1
predℤ≡-1 (pos zero)          = refl
predℤ≡-1 (pos (suc zero))    = refl
predℤ≡-1 (pos (suc (suc n))) = refl
predℤ≡-1 (negsuc n)          = cong (negsuc ∘ suc) $ sym $ ℕ.+-zero n

predℤ· : (a  b : ℤ) → predℤ a · b ≡ - b + a · b
predℤ· a b =
  predℤ a · b       ≡⟨ cong (_· b) (predℤ≡-1 a) ⟩
  (a - 1) · b       ≡⟨ cong (_· b) (+Comm a -1) ⟩
  (-1 + a) · b      ≡⟨ ·DistL+ -1 a b ⟩
  -1 · b + a · b    ≡⟨ cong (_+ a · b) (negsuc·ℤ 0 b) ⟩
  - (1 · b) + a · b ≡⟨ cong ((_+ a · b) ∘ -_) (·IdL b) ⟩
  - b + a · b       ∎

·predℤ : ∀ a b → a · predℤ b ≡ a · b - a
·predℤ a b = ·Comm a (predℤ b) ∙ predℤ· b a ∙ cong ((- a) +_) (·Comm b a) ∙ +Comm (- a) (a · b)

minus≡0- : (x : ℤ) → - x ≡ (0 - x)
minus≡0- (pos zero)    = refl
minus≡0- (pos (suc n)) = refl
minus≡0- (negsuc n)    = refl

absPos·Pos : (m n : ℕ) → abs (pos m · pos n) ≡ abs (pos m) ·ℕ abs (pos n)
absPos·Pos m n = refl

abs· : (m n : ℤ) → abs (m · n) ≡ abs m ·ℕ abs n
abs· (pos m)       (pos n)       = refl
abs· (pos zero)    (negsuc n)    = refl
abs· (pos (suc m)) (negsuc n)    = refl
abs· (negsuc m)    (pos zero)    = 0≡m·0 m
abs· (negsuc m)    (pos (suc n)) = refl
abs· (negsuc m)    (negsuc n)    = refl

sign·abs : ∀ m → sign m · pos (abs m) ≡ m
sign·abs (pos zero)    = refl
sign·abs (pos (suc n)) = cong (pos ∘ suc) (ℕ.+-zero n)
sign·abs (negsuc n)    = cong negsuc (ℕ.+-zero n)

-- ℤ is integral domain

isIntegralℤPosPos : (c m : ℕ) → pos c · pos m ≡ 0 → ¬ c ≡ 0 → m ≡ 0
isIntegralℤPosPos zero    m p c≠0 =  ⊥.rec (c≠0 refl)
isIntegralℤPosPos (suc c) m p _   = sym $ ℕ.0≡n·sm→0≡n $ injPos $
  pos 0               ≡⟨ sym p ⟩
  pos (suc c) · pos m ≡⟨ ·Comm (pos (suc c)) (pos m)  ⟩
  pos m · pos (suc c) ∎

isIntegralℤ : (c m : ℤ) → c · m ≡ 0 → ¬ c ≡ 0 → m ≡ 0
isIntegralℤ (pos zero)    (pos m)       p h = ⊥.rec (h refl)
isIntegralℤ (pos (suc c)) (pos m)       p h = cong pos (isIntegralℤPosPos (suc c) m p ℕ.snotz)
isIntegralℤ (pos zero)    (negsuc m)    p h = ⊥.rec (h refl)
isIntegralℤ (pos (suc c)) (negsuc m)    p h = ⊥.rec (negsucNotpos (predℕ (suc c ·ℕ suc m)) 0 p )
isIntegralℤ (negsuc c)    (pos zero)    p h = refl
isIntegralℤ (negsuc c)    (pos (suc m)) p h = ⊥.rec (negsucNotpos (predℕ (suc c ·ℕ suc m)) 0 p )
isIntegralℤ (negsuc c)    (negsuc m)    p h = ⊥.rec (ℕ.snotz (injPos p))

private
  ·lCancel-helper : (c m n : ℤ) → c · m ≡ c · n → c · (m - n) ≡ 0
  ·lCancel-helper c m n p =
      ·DistR+ c m (- n)
    ∙ (λ i → c · m + -DistR· c n (~ i))
    ∙ subst (λ a → c · m - a ≡ 0) p (-Cancel (c · m))

·lCancel : (c m n : ℤ) → c · m ≡ c · n → ¬ c ≡ 0 → m ≡ n
·lCancel c m n p h = -≡0 _ _ (isIntegralℤ c (m - n) (·lCancel-helper c m n p) h)

·rCancel : (c m n : ℤ) → m · c ≡ n · c → ¬ c ≡ 0 → m ≡ n
·rCancel c m n p h = ·lCancel c m n (·Comm c m ∙ p ∙ ·Comm n c) h

-Cancel'' : ∀ z → z ≡ - z → z ≡ 0
-Cancel'' z r = isIntegralℤ 2 z (
    2 · z         ≡⟨ ·DistL+ 1 1 z ⟩
    1 · z + 1 · z ≡⟨ cong₂ _+_ (·IdL z) (·IdL z) ⟩
    z + z         ≡⟨ cong (z +_) r ⟩
    z + - z       ≡⟨ -Cancel z ⟩
    0             ∎)
  λ r → ⊥.rec (snotz (injPos r))

-- some lemmas about finite sums

sumFinℤ0 : (n : ℕ) → sumFinℤ {n = n} (λ (x : Fin n) → 0) ≡ 0
sumFinℤ0 n = sumFinGen0 _+_ 0 +IdR n (λ _ → 0) λ _ → refl

sumFinℤHom : {n : ℕ} (f g : Fin n → ℤ)
  → sumFinℤ {n = n} (λ x → f x + g x) ≡ sumFinℤ {n = n} f + sumFinℤ {n = n} g
sumFinℤHom {n = n} = sumFinGenHom _+_ 0 +IdR +Comm +Assoc n
