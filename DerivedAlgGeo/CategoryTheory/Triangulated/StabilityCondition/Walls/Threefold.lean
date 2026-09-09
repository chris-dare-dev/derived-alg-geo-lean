/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Threefold.Basic

/-!
# Threefold walls

The four-coordinate compressed model of a polarised threefold and its
Bayer--Macrì--Toda charge, as a child of `Walls/ChargeFamily.lean`.  This is the
threefold counterpart of `Walls/Numerical/`, which does the same for surfaces in
three coordinates.

Declarations use the strong-child namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall`,
inside a `Threefold` namespace so that its `NumClass`, `reZ` and `imZ` do not
collide with the surface ones.

The BMT inequality is not asserted anywhere in this subtree; it is false in
general, and `AlgebraicGeometry/Numerical/Stability/BMT.lean` carries it as
supplied data with that warning.
-/
