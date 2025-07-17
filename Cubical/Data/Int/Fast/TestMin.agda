{-# OPTIONS --safe #-}
module Cubical.Data.Int.Fast.TestMin where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ
  hiding   (+-assoc ; +-comm ; min ; max ; minComm ; maxComm)
  renaming (_·_ to _·ℕ_; _+_ to _+ℕ_ ; ·-assoc to ·ℕ-assoc ;
            ·-comm to ·ℕ-comm ; isEven to isEvenℕ ; isOdd to isOddℕ)
open import Cubical.Data.Sum

-- test for faster min
open import Agda.Builtin.Bool as B using ()
open import Agda.Builtin.Nat using () renaming ( _<_ to _<ᵇ_ )  

ℕmin' : ℕ → ℕ → ℕ
ℕmin' m n with (m <ᵇ n)
...          | B.false = n
...          | B.true  = m

{- old test
_<ᵗ_ : ℕ → ℕ → Type
_<ᵗ_ m n with m <ᵇ n
... | B.false = ⊥
... | B.true = Unit

private
  helperL : ∀ m n → m <ᵗ n → ℕ.min m n ≡ m  
  helperL zero    (suc n) p = refl
  helperL (suc m) (suc n) p = cong suc $ helperL m n p

  helperR : ∀ m n → n <ᵗ m → ℕ.min m n ≡ n  
  helperR (suc m) zero p    = refl
  helperR (suc m) (suc n) p = cong suc $ helperR m n p

  data Trichotomy< : ℕ → ℕ → Type where
    is< : ∀ m n → m <ᵗ n → Trichotomy< m n
    is= : ∀ m n → m ≡ n  → Trichotomy< m n
    is> : ∀ m n → n <ᵗ m → Trichotomy< m n  
  
  cases< : ∀ m n → Trichotomy< m n
  cases< zero    zero    = is= zero zero refl
  cases< zero    (suc n) = is< zero (suc n) tt
  cases< (suc m) zero    = is> (suc m) zero tt
  cases< (suc m) (suc n) with cases< m n
  ...                       | is< m n w = is< (suc m) (suc n) w
  ...                       | is= m n p = is= (suc m) (suc n) (cong suc p)
  ...                       | is> m n w = is> (suc m) (suc n) w
  
  -- slow, but the reason is that cases< is slow,
  -- if we can write a version of cases< by case splitting at _<ᵇ_,
  -- this should become as fast as ℕmin, without having the proofs too long 
  minw : ℕ → ℕ → ℕ
  minw m n with cases< m n
  ... | is< m n x = m
  ... | is= m n x = m
  ... | is> m n x = n

  minIdemPath : ∀ m n → m ≡ n → ℕ.min m n ≡ m
  minIdemPath zero    n       p = refl
  minIdemPath (suc m) zero    p = ⊥.rec (ℕ.snotz p)
  minIdemPath (suc m) (suc n) p =  cong suc $ minIdemPath m n (ℕ.injSuc p)

  -- easy to reason with it
  minw≡min : ∀ m n → minw m n ≡ ℕ.min m n
  minw≡min m n with cases< m n
  ... | is< m n x = sym $ helperL m n x
  ... | is= m n x = sym $ minIdemPath m n x
  ... | is> m n x = sym $ helperR m n x
-}

private
  helperSplit : ∀ m n → Σ[ b ∈ B.Bool ] (m <ᵇ n) ≡ b
  helperSplit m n with m <ᵇ n
  ... | B.false = B.false , refl
  ... | B.true  = B.true  , refl

  false≠true : ¬ (B.false ≡ B.true)
  false≠true p = transport (λ i → T (p i)) tt  where
    T : B.Bool → Type
    T B.false = Unit
    T B.true  = ⊥

  true≠false : ¬ (B.true ≡ B.false)
  true≠false p = false≠true $ sym p

min''Helper : B.Bool → ℕ → ℕ → ℕ
min''Helper B.false m n = n -- constant time
min''Helper B.true  m n = m -- constant time

min'' : ℕ → ℕ → ℕ
min'' m n = min''Helper (m <ᵇ n) m n -- _<ᵇ_ is builtin, so it should be logarithmic time(?)  

private
  -- linear time! ( linear in min(m,n), since as soon as one of m or n is zero, it is constant )
  <ᵇ≡true→minL : ∀ m n → (m <ᵇ n) ≡ B.true → ℕ.min m n ≡ m
  <ᵇ≡true→minL zero    zero    p = refl
  <ᵇ≡true→minL zero    (suc n) p = refl
  <ᵇ≡true→minL (suc m) zero    p = ⊥.rec (false≠true p )
  <ᵇ≡true→minL (suc m) (suc n) p = cong suc (<ᵇ≡true→minL m n p) -- recursion!

  -- linear time!
  <ᵇ≡false→minR : ∀ m n → (m <ᵇ n) ≡ B.false → ℕ.min m n ≡ n
  <ᵇ≡false→minR zero    zero    p = refl
  <ᵇ≡false→minR zero    (suc n) p = ⊥.rec (true≠false p)
  <ᵇ≡false→minR (suc m) zero    p = refl
  <ᵇ≡false→minR (suc m) (suc n) p = cong suc (<ᵇ≡false→minR m n p) -- recursion!
  
-- log + linear = linear time!
min≡min'' : ∀ m n → ℕ.min m n ≡ min'' m n
min≡min'' m n with helperSplit m n -- builtin, so it should be logarithmic time(?)  
...              | B.false , r = <ᵇ≡false→minR m n r ∙ subst (λ b → n ≡ min''Helper b m n) (sym r) refl -- recursion! 
...              | B.true  , r = <ᵇ≡true→minL m n r  ∙ subst (λ b → m ≡ min''Helper b m n) (sym r) refl -- recursion!

-- logarithmic time !
min''≡min' : ∀ m n → min'' m n ≡ ℕmin' m n
min''≡min' m n with m <ᵇ n         -- builtin, so it should be logarithmic time(?)  
...               | B.false = refl -- constant time!
...               | B.true  = refl -- constant time!

-- linear time! 
min≡min' : ∀ m n → ℕ.min m n ≡ ℕmin' m n
min≡min' m n = min≡min'' m n ∙ min''≡min' m n

-- linear time!
¬<ᵇ∧¬>ᵇ→≡ : ∀ m n → (m <ᵇ n) ≡ B.false → (n <ᵇ m) ≡ B.false → m ≡ n 
¬<ᵇ∧¬>ᵇ→≡ zero    zero    p q = refl
¬<ᵇ∧¬>ᵇ→≡ zero    (suc n) p q = ⊥.rec (true≠false p)
¬<ᵇ∧¬>ᵇ→≡ (suc m) zero    p q = ⊥.rec (true≠false q)
¬<ᵇ∧¬>ᵇ→≡ (suc m) (suc n) p q = cong suc $ ¬<ᵇ∧¬>ᵇ→≡ m n p q -- recursion call: not fast!

-- linear time! 
<ᵇ∧>ᵇ→⊥ : ∀ m n → (m <ᵇ n) ≡ B.true → (n <ᵇ m) ≡ B.true → ⊥
<ᵇ∧>ᵇ→⊥ zero    zero    p q = false≠true p
<ᵇ∧>ᵇ→⊥ zero    (suc n) p q = false≠true q
<ᵇ∧>ᵇ→⊥ (suc m) zero    p q = false≠true p
<ᵇ∧>ᵇ→⊥ (suc m) (suc n) p q = <ᵇ∧>ᵇ→⊥ m n p q -- recursion call

-- linear time!
min''Comm : ∀ n m → min'' n m ≡ min'' m n
min''Comm n m with helperSplit n m | helperSplit m n
... | B.false , p | B.false , q = subst (λ b → min''Helper b n m ≡ m) (sym p) refl
                               ∙∙ ¬<ᵇ∧¬>ᵇ→≡ m n q p -- here it uses the recursion call!
                               ∙∙ subst (λ b → n ≡ min''Helper b m n) (sym q) refl 
... | B.false , p | B.true  , q = subst (λ b → min''Helper b n m ≡ m) (sym p) refl
                                ∙ subst (λ b → m ≡ min''Helper b m n) (sym q) refl
... | B.true  , p | B.false , q = subst (λ b → min''Helper b n m ≡ n) (sym p) refl
                                ∙ subst (λ b → n ≡ min''Helper b m n) (sym q) refl
... | B.true  , p | B.true  , q = ⊥.rec (<ᵇ∧>ᵇ→⊥ n m p q) --here it uses the recursion call!

-- Conclusion:
-- ∙ min             is  linear
-- ∙ ℕmin' and min'' are logarithmic
-- ∙ min''Comm       is  linear, IF evaluated to concrete naturals

-- So it is possible that a lot of properties will not be fast,
-- whilst the evaluation at large naturals (and by extension to
-- large integers) will be fast.

-- We have to understand how import it is to make the properties fast,
-- because it could be that they are used as a witness to some algorithm,
-- without inspecting them, so declaring them as abstract/opaque could
-- help to make such algorithms fast

-- IDEA: define it i a symmetric way: case split both on m <ᵇ n AND n <ᵇ m
-- it will be techincally slower (If it was C log(min(m,n)) it will become 2 times that),
-- but the constants are not so import, and it could make the proof both easier are faster!

{- we still can't prove the commutativity in logarithmic time!   
min''' : ℕ → ℕ → ℕ
min''' m n with m <ᵇ n  | n <ᵇ m
...           | B.false | B.false = n -- here m and n must be equal, se we will set whatever
...           | B.false | B.true  = n
...           | B.true  | B.false = m
...           | B.true  | B.true  = 0 -- impossible clause, we will set 0, since it does not dependp on either

min'''Comm : ∀ m n → min''' m n ≡ min''' n m
min'''Comm m n with m <ᵇ n  | n <ᵇ m
...               | B.false | B.false = {!!} -- we are stuck without the helperSplit
                                             -- and in any cases we would need ¬<ᵇ∧¬>ᵇ→≡, which is too slow
...               | B.false | B.true  = refl
...               | B.true  | B.false = refl
...               | B.true  | B.true  = refl
-}
