{-# OPTIONS --safe #-}
module Cubical.Data.Int.Perf where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int.Base

-- _ : 123 ·f (- 456) ≡ - 56088
-- _ = refl

_ : 123 -f 456789 ≡ -456666
_ = refl
