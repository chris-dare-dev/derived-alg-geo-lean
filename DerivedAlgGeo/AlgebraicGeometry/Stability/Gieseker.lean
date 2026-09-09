/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.Basic
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.Coefficients
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.HarderNarasimhan
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.HilbertPolynomial
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.MuStability

/-! # Gieseker stability of coherent sheaves

The Hilbert function of a coherent sheaf against a supplied polarization, its Newton
coefficients, the purity and Gieseker stability notions built from them, and the weak slope
datum through which `Coh X` becomes an inhabitant of the abstract slope theory.

Harder–Narasimhan filtrations for the resulting slope, and the maximal destabilizing subobject
they are built from, are not here.
-/
