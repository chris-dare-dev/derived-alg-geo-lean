/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PeriodDomain
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PositivePairOpen
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.Continuous
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.Bounds
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.SignatureAdditive
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.WallFiniteness
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.WallRegion
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.ComplexPairing
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.ComplexPairingSignature
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.CutNonempty
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.Orientation
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.OrientationCocycle

/-! # Quadratic forms

Signature theory of real quadratic spaces, and the period domain a signature
`(2, n - 2)` space carries.
-/
