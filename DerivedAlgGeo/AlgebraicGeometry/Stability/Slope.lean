/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Slope.Basic
import DerivedAlgGeo.AlgebraicGeometry.Stability.Slope.HarderNarasimhan

/-! # μ-slope stability of coherent sheaves

The weak slope datum `Coh X` carries against a polarization — rank is the Hilbert multiplicity,
degree is the Hilbert degree coefficient — together with the maximal destabilizing subobject and
the Harder–Narasimhan filtration it generates.

This is a sibling of `Gieseker/`, not a child and not a parent. Both are built on the shared
Hilbert-polynomial data one directory up (`HilbertPolynomial.lean`, `Coefficients.lean`,
`Purity.lean`); neither imports the other; and every statement that mentions both lives in
`Comparison.lean`. The Harder–Narasimhan theorems below are theorems about the **μ-slope** and
say nothing about Gieseker stability.
-/
