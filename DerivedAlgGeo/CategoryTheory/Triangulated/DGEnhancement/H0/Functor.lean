/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Functor

/-!
# Compatibility import for shift preservation by dg functors

`DGFunctor.PreservesShifts` is owned by the pretriangulated dg layer and is
re-exported here for compatibility.  The constructions transporting it to the
chosen shift functors on `H⁰` currently live in `H0.Triangle` and will move into
this module when that compilation unit is split by responsibility.
-/
