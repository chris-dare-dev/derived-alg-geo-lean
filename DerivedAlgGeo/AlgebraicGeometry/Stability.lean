/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker

/-! # Stability of sheaves

Slope and Gieseker stability of coherent sheaves on a polarized variety, and their
Harder–Narasimhan theory, built on `Coh X` and the Euler characteristic.

This subtree is deliberately distinct from `AlgebraicGeometry/StabilityCondition/`, whose
modules are all `Families/**` and belong to the derived-category lane on `Dqc`. Nothing
here is added to that umbrella, and nothing here imports the abstract stability-condition
tree: the objects are sheaves, the invariants are Hilbert polynomials, and the connection
to `WeakSlopeData` and the tilted-heart constructions is made by later issues in this lane,
not by this umbrella.
-/
