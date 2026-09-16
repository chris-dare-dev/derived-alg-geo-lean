/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Coefficients
import DerivedAlgGeo.AlgebraicGeometry.Stability.Comparison
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker
import DerivedAlgGeo.AlgebraicGeometry.Stability.HilbertPolynomial
import DerivedAlgGeo.AlgebraicGeometry.Stability.Purity
import DerivedAlgGeo.AlgebraicGeometry.Stability.Slope

/-! # Stability of sheaves

Slope and Gieseker stability of coherent sheaves on a polarized variety, and the
Harder–Narasimhan theory of the μ-slope, built on `Coh X` and the Euler characteristic.

## The shape of the subtree

`HilbertPolynomial.lean`, `Coefficients.lean` and `Purity.lean` are the **shared data**: the
polarization datum, the Hilbert function, its Newton coefficients, and purity. `Slope/` and
`Gieseker/` are **siblings** built on them, neither importing the other, and `Comparison.lean` is
the one module that mentions both. MO1.08 (#1319) put it in that shape; before it, the μ-slope
theory and the μ-Harder–Narasimhan existence theorem were children of `Gieseker/`, which named
them after a theory they do not use.

## What this subtree is not

It is deliberately distinct from `AlgebraicGeometry/StabilityCondition/`, whose modules are all
`Families/**` and belong to the derived-category lane on `Dqc`. Nothing here is added to that
umbrella.

Nor does anything here reach `CategoryTheory/Triangulated/StabilityCondition/`. The abstract
slope theory `Slope/` instantiates is abelian and lives at
`CategoryTheory/Abelian/Stability/`; sheaves, Hilbert polynomials and slopes need no
t-structure. The only module that crosses into the derived category is
`Slope/HarderNarasimhan/HeartTransport.lean`, which reads the μ-slope on the heart of the
canonical t-structure on `D(Coh X)` and is a leaf.
-/
