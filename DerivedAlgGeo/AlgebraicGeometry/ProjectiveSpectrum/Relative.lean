/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Relative.Basic
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Relative.Bundle
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Relative.Functoriality
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Relative.GradedAlgebraData

/-!
# Relative `Proj`

The relative `Proj` of a quasi-coherent graded `𝒪_S`-algebra (Stacks, Section 27.15).

* `Relative/GradedAlgebraData.lean`: `AlgebraicGeometry.Scheme.QuasicoherentGradedAlgebraData`,
  quasi-coherent graded algebras as affine-local data, and the symmetric algebra `sym E` of a
  quasi-coherent module sheaf.
* `Relative/Basic.lean`: `QuasicoherentGradedAlgebraData.relativeProj`, glued from `Proj 𝒜(U)`
  over the affine opens `U`, with `π⁻¹(U) ≅ Proj 𝒜(U)`, and separatedness of `π`.
* `Relative/Functoriality.lean`: the category of quasi-coherent graded algebras and
  `QuasicoherentGradedAlgebraData.relativeProjMap`, the morphism of relative `Proj`s induced by a
  graded map, a closed immersion for a chartwise surjective map.
* `Relative/Bundle.lean`: `Scheme.projectiveBundle E = Proj_S(Sym E)`, and the closed immersion
  `P(F) ⟶ P(E)` induced by an epimorphism `E ⟶ F`.
-/
