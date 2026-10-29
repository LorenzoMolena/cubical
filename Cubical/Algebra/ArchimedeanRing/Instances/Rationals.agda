module Cubical.Algebra.ArchimedeanRing.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.ArchimedeanRing
open import Cubical.Algebra.ArchimedeanField

open import Cubical.Algebra.ArchimedeanField.Instances.Rationals
open ArchimedeanFieldTheory

ℚArchimedeanRing : ArchimedeanRing ℓ-zero ℓ-zero
ℚArchimedeanRing = ArchimedeanField→ArchimedeanRing ℚArchimedeanField
