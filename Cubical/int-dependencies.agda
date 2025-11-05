{-# OPTIONS --safe --cubical --no-import-sorts -WnoUnsupportedIndexedMatch --guardedness #-}
module Cubical.int-dependencies where

open import Cubical.Algebra.AbGroup.FinitePresentation -- ✓
open import Cubical.Algebra.AbGroup.Instances.DiffInt
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.AbGroup.Instances.Int      -- replace with the one below
open import Cubical.Algebra.AbGroup.Instances.Fast.Int -- ✓
open import Cubical.Algebra.AbGroup.Instances.IntMod
open import Cubical.Algebra.AbGroup.Properties
open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.CommRing.Instances.BiInvInt
open import Cubical.Algebra.CommRing.Instances.Int      -- replace with the one below:
open import Cubical.Algebra.CommRing.Instances.Fast.Int -- ✓
open import Cubical.Algebra.CommRing.Instances.QuoInt
open import Cubical.Algebra.Field.Instances.Rationals
open import Cubical.Algebra.Group.Instances.DiffInt
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Group.ZAction
open import Cubical.Algebra.IntegerMatrix.Base -- ✓
open import Cubical.Algebra.IntegerMatrix.Diagonalization -- ✓
open import Cubical.Algebra.IntegerMatrix.Elementaries -- ✓
open import Cubical.Algebra.IntegerMatrix.Smith.NormalForm -- ✓
open import Cubical.Algebra.IntegerMatrix.Smith.Normalization -- × , needs an hiding
open import Cubical.CW.ChainComplex
open import Cubical.CW.Homology.Base
open import Cubical.CW.Homology.Groups.CofibFinSphereBouquetMap
open import Cubical.CW.Homology.Groups.Sn
open import Cubical.CW.Homology.Groups.Subcomplex
open import Cubical.CW.Homotopy
open import Cubical.CW.HurewiczTheorem
open import Cubical.CW.Map
open import Cubical.Cohomology.Base
open import Cubical.Cohomology.EilenbergMacLane.EilenbergSteenrod
open import Cubical.Data.Equality.S1  -- ✓
-- open import Cubical.Data.Int
-- open import Cubical.Data.Int.Base
-- open import Cubical.Data.Int.Divisibility
-- open import Cubical.Data.Int.Fast.Base
-- open import Cubical.Data.Int.Fast.Divisibility
-- open import Cubical.Data.Int.Fast.IsEven
-- open import Cubical.Data.Int.Fast.Properties
-- open import Cubical.Data.Int.IsEven
open import Cubical.Data.Int.MoreInts.BiInvInt
open import Cubical.Data.Int.MoreInts.BiInvInt.Base
open import Cubical.Data.Int.MoreInts.BiInvInt.Properties
open import Cubical.Data.Int.MoreInts.DeltaInt
open import Cubical.Data.Int.MoreInts.DeltaInt.Base
open import Cubical.Data.Int.MoreInts.DeltaInt.Properties
open import Cubical.Data.Int.MoreInts.DiffInt
open import Cubical.Data.Int.MoreInts.DiffInt.Base
open import Cubical.Data.Int.MoreInts.DiffInt.Properties
open import Cubical.Data.Int.MoreInts.QuoInt
open import Cubical.Data.Int.MoreInts.QuoInt.Base
open import Cubical.Data.Int.MoreInts.QuoInt.Properties
-- open import Cubical.Data.Int.Order
-- open import Cubical.Data.Int.Properties
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.MoreRationals.HITQ.Base
open import Cubical.Data.Rationals.MoreRationals.LocQ.Base
open import Cubical.Data.Rationals.MoreRationals.QuoQ.Base
open import Cubical.Data.Rationals.MoreRationals.QuoQ.Properties
open import Cubical.Data.Rationals.MoreRationals.SigmaQ.Base
open import Cubical.Data.Rationals.MoreRationals.SigmaQ.Properties
open import Cubical.Data.Rationals.Order
open import Cubical.Data.Rationals.Properties
open import Cubical.Experiments.CohomologyGroups -- ✓
open import Cubical.Experiments.Generic -- ✓
open import Cubical.Experiments.HInt -- ✓
open import Cubical.Experiments.IntegerMatrix -- ✓
open import Cubical.Experiments.IsoInt.Base -- ✓
open import Cubical.Experiments.Problem -- ✓
open import Cubical.Experiments.ZCohomology.Benchmarks -- ✓
open import Cubical.Experiments.ZCohomologyOld.Base -- ✓
open import Cubical.Experiments.ZCohomologyOld.KcompPrelims -- ✓
open import Cubical.Experiments.ZCohomologyOld.Properties -- × , problem on line 500
open import Cubical.HITs.FreeGroup.Properties
open import Cubical.HITs.KleinBottle.Properties
open import Cubical.HITs.S1.Base -- × , but now is fixed
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.HITs.Torus.Base
open import Cubical.Homotopy.EilenbergSteenrod
open import Cubical.Homotopy.Group.Pi3S2
open import Cubical.Homotopy.Group.Pi4S3.BrunerieExperiments
open import Cubical.Homotopy.Group.Pi4S3.BrunerieNumber
open import Cubical.Homotopy.Group.Pi4S3.DirectProof
open import Cubical.Homotopy.Group.Pi4S3.Summary
open import Cubical.Homotopy.Group.PiAbCofibFinSphereBouquetMap
open import Cubical.Homotopy.Group.PiCofibFinSphereBouquetMap
open import Cubical.Homotopy.Group.PinSn
open import Cubical.Homotopy.Hopf
open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.HopfInvariant.Brunerie
open import Cubical.Homotopy.HopfInvariant.Homomorphism
open import Cubical.Homotopy.HopfInvariant.HopfMap
open import Cubical.Homotopy.Prespectrum
open import Cubical.Homotopy.Spectrum
open import Cubical.Homotopy.Spectrum.Fiber
open import Cubical.Homotopy.Spectrum.Truncation
open import Cubical.Papers.Pi4S3 -- ✓
open import Cubical.Papers.RepresentationIndependence -- × : problem on line 241.
  -- easy to fix, but it would have been better if we could avoid to edit Papers
open import Cubical.Papers.Synthetic
open import Cubical.Papers.ZCohomology
open import Cubical.Relation.Binary.Order.Loset.Instances.Int
open import Cubical.Relation.Binary.Order.Toset.Instances.Int
open import Cubical.Structures.Successor
open import Cubical.Tactics.CommRingSolver.EvalHom
open import Cubical.Tactics.CommRingSolver.Examples
open import Cubical.Tactics.CommRingSolver.HornerEval
open import Cubical.Tactics.CommRingSolver.HornerForms
open import Cubical.Tactics.CommRingSolver.IntAsRawRing
open import Cubical.Tactics.CommRingSolver.RawAlgebra
open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Talks.EPA2020
open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.CohomologyRings.CP2
open import Cubical.ZCohomology.CohomologyRings.CupProductProperties
open import Cubical.ZCohomology.CohomologyRings.KleinBottle
open import Cubical.ZCohomology.CohomologyRings.RP2
open import Cubical.ZCohomology.CohomologyRings.RP2wedgeS1
open import Cubical.ZCohomology.CohomologyRings.S1
open import Cubical.ZCohomology.CohomologyRings.S2wedgeS4
open import Cubical.ZCohomology.CohomologyRings.Sn
open import Cubical.ZCohomology.CohomologyRings.Unit
open import Cubical.ZCohomology.EilenbergSteenrodZ
open import Cubical.ZCohomology.GroupStructure -- 4 proofs to fix
open import Cubical.ZCohomology.Groups.CP2
open import Cubical.ZCohomology.Groups.Connected -- ✓
open import Cubical.ZCohomology.Groups.KleinBottle
open import Cubical.ZCohomology.Groups.Prelims
open import Cubical.ZCohomology.Groups.RP2
open import Cubical.ZCohomology.Groups.RP2wedgeS1
open import Cubical.ZCohomology.Groups.S2wedgeS1wedgeS1
open import Cubical.ZCohomology.Groups.S2wedgeS4
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Torus
open import Cubical.ZCohomology.Groups.Unit -- ✓
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Gysin
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.GradedCommutativity
open import Cubical.ZCohomology.RingStructure.RingLaws
