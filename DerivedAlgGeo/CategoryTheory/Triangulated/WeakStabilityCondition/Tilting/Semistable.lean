/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Semistable.TiltGeometry
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Semistable.TiltedHeart
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Semistable.ZeroCharge
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Semistable.SemistableTransfer
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Semistable.Classification

/-!
# Semistable objects after tilting a weak stability condition

This umbrella exports the phase-language counterpart of Lemma 14.17 of
arXiv:1902.08184v4.  The slope cutoff in the paper is represented by a phase
cutoff `beta` in `[0, 1)`, as in
`WeakStabilityCondition/Tilting/TorsionPair/Slope.lean`.  The converse uses
`0 < beta`, since a finite slope cutoff corresponds to a phase cut strictly
inside `(0, 1)`.  The numerical reparameterisation between the two cutoffs is
deliberately not asserted.

The development is owned by five modules:

* `Semistable.TiltGeometry` -- rotation through `pi * beta`, the rotated
  charge, the closed weak upper half plane, the cross product, and the strict
  slope comparisons from phase separation;
* `Semistable.TiltedHeart` -- the HRS-tilted heart identified by its old phase
  interval, its agreement with the phase-shifted heart, and the weak stability
  function it carries;
* `Semistable.ZeroCharge` -- the degenerate zero-charge locus and vanishing of
  maps out of it;
* `Semistable.SemistableTransfer` -- semistability transfer in the torsion,
  torsion-free, and fixed-ray cases;
* `Semistable.Classification` -- the two source-shaped classes, both directions
  of Lemma 14.17, and the resulting characterisation.

Every object of the tilted heart has all old slicing phases in
`(beta, beta + 1]`; decomposing it into its old HN factors therefore proves
the weak upper-half-plane condition directly, including zero-charge factors.
The converse is proved by factoring maps through their image in the abelian
tilted heart: positive imaginary charge gives the semistable case, and the
strict `IsStable` predicate gives the boundary case.

Importing this module is equivalent to the former single-file surface; new
code should prefer the narrowest owning module above.
-/
