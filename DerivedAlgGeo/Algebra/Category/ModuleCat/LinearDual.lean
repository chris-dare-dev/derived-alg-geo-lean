/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.LinearDual.Basic
import DerivedAlgGeo.Algebra.Category.ModuleCat.LinearDual.Exact

/-! # Algebraic linear duality on `ModuleCat`

`Basic` bundles Mathlib's `Module.Dual` and `LinearMap.dualMap` as a
contravariant additive functor; `Exact` proves it exact over a field. Both
extend `Mathlib/Algebra/Category/ModuleCat/`, which is where `ModuleCat` is
defined, so both live here. The derived lift is
`Algebra/Homology/DerivedCategory/LinearDual.lean`. -/
