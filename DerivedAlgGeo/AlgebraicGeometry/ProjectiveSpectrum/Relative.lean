/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Relative.Basic
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Relative.GradedAlgebraData

/-!
# Relative `Proj`

The relative `Proj` of a quasi-coherent graded `𝒪_S`-algebra (Stacks, Section 27.15).

* `Relative/GradedAlgebraData.lean`: `AlgebraicGeometry.Scheme.QuasicoherentGradedAlgebraData`,
  quasi-coherent graded algebras as affine-local data, and the symmetric algebra `sym E` of a
  quasi-coherent module sheaf.
* `Relative/Basic.lean`: `QuasicoherentGradedAlgebraData.relativeProj`, glued from `Proj 𝒜(U)`
  over the affine opens `U`, with `π⁻¹(U) ≅ Proj 𝒜(U)`.
-/
