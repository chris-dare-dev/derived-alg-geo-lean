/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.ExteriorPower
import DerivedAlgGeo.LinearAlgebra.BilinearForm
import DerivedAlgGeo.LinearAlgebra.Complex.Coordinates
import DerivedAlgGeo.LinearAlgebra.GradedBasis
import DerivedAlgGeo.LinearAlgebra.Lattice
import DerivedAlgGeo.LinearAlgebra.Matrix.GeneralLinearGroup.Positive
import DerivedAlgGeo.LinearAlgebra.Matrix.GeneralLinearGroup.UniversalCover
import DerivedAlgGeo.LinearAlgebra.Matrix.PolarDecomposition
import DerivedAlgGeo.LinearAlgebra.QuadraticForm
import DerivedAlgGeo.LinearAlgebra.FiniteDimensional

/-! # Linear algebra

Exterior powers, weighted-basis decompositions, lattice theory, Mukai
constructions, quadratic-form signature theory, and matrix infrastructure used
throughout the repository, including the universal cover of `GL⁺(2, ℝ)`
beside the general-linear-group API it covers.
-/
