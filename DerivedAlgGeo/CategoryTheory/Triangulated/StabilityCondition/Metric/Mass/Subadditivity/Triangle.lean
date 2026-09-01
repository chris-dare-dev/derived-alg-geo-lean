/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.Triangle.HeartObservable
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.Triangle.MassTransport
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.Triangle.MassAdditivity
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.Triangle.HeartShortExact
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.Triangle.PhaseOne
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.Triangle.Consequences

/-!
# The Harder--Narasimhan mass-triangle chain

This umbrella exports the stronger HN-mass subadditivity route selected for the
repository's topology comparison around Bridgeland's Proposition 8.1.  The
chain is developed in six owned modules:

* `Triangle.HeartObservable` -- the bridge from a stability condition with an
  arbitrary class map to a `StabilityFunction` on its canonical heart, and the
  agreement of heart semistability with the ambient slicing;
* `Triangle.MassTransport` -- the charge-norm bound and the behaviour of mass
  under shifts, lifted rotations, and appended factors;
* `Triangle.MassAdditivity` -- exact additivity of mass along a phase-separated
  or boundary-cut distinguished triangle, and the inequalities that follow
  directly;
* `Triangle.HeartShortExact` -- the named `Prop`-valued targets, the short
  exact sequence to distinguished triangle bridge, and the phase-one
  boundary-heart inequality;
* `Triangle.PhaseOne` -- the six-term `H⁰` comparison for a phase-one left
  endpoint, isolated for elaboration cost;
* `Triangle.Consequences` -- removal of the phase-one hypothesis by head--tail
  octahedral induction, the named milestones, and the unconditional topology
  comparison.

`HNPolygon` supplies the ambient convex hull and distinguished HN path.
`ConvexPolygonPerimeter` proves the independent `t = 0` comparison of closed
vertex polygons, proves that positive-angle support maxima of the ambient HN
polygon occur on the HN path, and derives the boundary-cut mass comparison for
monomorphisms and short exact sequences. `H0ExactnessBridge` identifies the
exact heart-source obstruction as a canonical cokernel map being monic and
discharges it by proving the canonical `H⁰` and `H⁰'` functors homological.
No open premise is assumed as an instance or axiom.

Importing this module is equivalent to the former single-file surface; new
code should prefer the narrowest owning module above.
-/
