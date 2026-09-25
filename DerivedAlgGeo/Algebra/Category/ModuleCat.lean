/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Presheaf
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf
import DerivedAlgGeo.Algebra.Category.ModuleCat.LinearDual
import DerivedAlgGeo.Algebra.Category.ModuleCat.Limits
import DerivedAlgGeo.Algebra.Category.ModuleCat.Noetherian
import DerivedAlgGeo.Algebra.Category.ModuleCat.ProjectiveResolution
import DerivedAlgGeo.Algebra.Category.ModuleCat.Localization

/-!
# Categories of modules

Extensions of Mathlib's `ModuleCat`, including canonical localization, and of
`PresheafOfModules` and `SheafOfModules` on an arbitrary ringed site.
Scheme-indexed module sheaves, quasicoherent and coherent sheaves, and
everything else whose signature mentions a scheme lives under
`AlgebraicGeometry/Modules/`.
-/
