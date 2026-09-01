/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Uniqueness.MonoDescent
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Uniqueness.SubobjectLattice
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Uniqueness.Extrema
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Uniqueness.Tail
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Uniqueness.Destabilizing

/-!
# Uniqueness of owner Harder--Narasimhan filtrations

This umbrella exports the owner-native uniqueness argument, owned by five
modules:

* `Uniqueness.MonoDescent` -- normalization of phase and semistability under
  rewriting of a successive quotient, transport of subobjects along a
  monomorphism, extension of an HN filtration along a mono, and the semistable
  base case;
* `Uniqueness.SubobjectLattice` -- one factor exactly when semistable, the
  compatibility of pullback along a cokernel projection with the chain and with
  charge, and the comparison `cokernelPullbackIso`;
* `Uniqueness.Extrema` -- the first chain step as the maximal semistable
  subobject of maximal phase, and the formulas `phiPlus_eq`, `phiMinus_eq`;
* `Uniqueness.Tail` -- the tail filtration and the invariance of the number of
  factors;
* `Uniqueness.Destabilizing` -- the maximally destabilizing subobject, its
  quotient and short exact sequence, and the extremal phase functions `phiPlus`
  and `phiMinus` with the characterisation of semistability.

Importing this module is equivalent to the former single-file surface; new
code should prefer the narrowest owning module above.
-/
