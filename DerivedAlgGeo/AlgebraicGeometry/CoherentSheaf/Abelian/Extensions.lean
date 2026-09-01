/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Abelian.Kernels
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Extensions

/-!
# Extensions of coherent sheaves

Finite presentation of module sheaves is closed under extensions on an arbitrary ringed site;
the categorical proof lives in
`DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Extensions`. This file applies
that result to the coherent object property on a scheme.

## Main result

* `Scheme.coherent_isClosedUnderExtensions`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- Coherent module sheaves are closed under extensions. -/
noncomputable instance coherent_isClosedUnderExtensions :
    (coherent X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ :=
    SheafOfModules.IsFinitePresentation.middle_of_shortExact.{u} hS h₁ h₃

end AlgebraicGeometry.Scheme
