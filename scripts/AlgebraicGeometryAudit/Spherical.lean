/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Surface.SphericalCategorical

/-!
Audit records for the K3 spherical bridge.
-/

/-! ## The K3 profile is an abstract spherical object (#888)

One-way only. The abstract predicate has no canonical bundle and so no `E ⊗ omega_X ≅ E` content;
on a K3 that clause is automatic because omega_X is trivial, which is why the K3 profile omits it.
The two omissions have DIFFERENT reasons -- triviality there, vacuity here -- so a converse would
have to invent the first from the second.

The Euler agreement is not definitional: `selfEuler` is a bespoke three-term sum over degrees
0, 1, 2 while `chiHom` is a finsum over all of the integers. They agree for a spherical object
because both compute 2, and they need not agree for a non-spherical one. -/

#print axioms AlgebraicGeometry.K3Surface.SphericalExtProfile.isSphericalObject
#print axioms AlgebraicGeometry.K3Surface.SphericalExtProfile.selfEuler_eq_chiHom
