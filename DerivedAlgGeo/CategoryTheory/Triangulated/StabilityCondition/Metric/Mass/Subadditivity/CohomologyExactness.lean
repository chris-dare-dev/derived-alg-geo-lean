/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Cohomology.Sequence

/-!
# Owner-native cohomology exactness

The original version of this module adapted the retained
`HeartStabilityData` API to Mathlib's homological-functor interface.  The
repository now proves homologicality and the shifted cohomology sequences
directly for `originalHeartCohFunctor`; importing the owner sequence module is
the complete public boundary needed by mass subadditivity.
-/
