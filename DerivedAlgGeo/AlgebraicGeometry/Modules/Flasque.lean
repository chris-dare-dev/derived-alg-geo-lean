/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.Topology.Sheaves.Flasque

/-!
# Injective module sheaves on a scheme are flasque

`SheafOfModules.isFlasque_toSheaf_of_injective` transported across the wrapper `X.Modules`,
whose category instance is a copy of that of `SheafOfModules X.ringCatSheaf`, so that
`Injective` must be carried across by hand. The consequence for cohomology is that an
injective `𝒪_X`-module is acyclic for `Sheaf.H`, by `TopCat.Sheaf.subsingleton_H_of_isFlasque`.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- `Injective` for the wrapper `X.Modules` is `Injective` for `SheafOfModules`: the
category structures agree on the nose. -/
theorem injective_sheafOfModules_of_injective (I : X.Modules) [hI : Injective I] :
    Injective (show SheafOfModules.{u} X.ringCatSheaf from I) where
  factors {A B} g f hf :=
    @Injective.factors X.Modules _ I hI A B g f ⟨fun _ _ h ↦ hf.right_cancellation _ _ h⟩

/-- **Injective module sheaves on a scheme are flasque.** -/
theorem isFlasque_toSheaf_of_injective (I : X.Modules) [Injective I] :
    TopCat.Sheaf.IsFlasque ((toSheaf X).obj I) :=
  haveI := injective_sheafOfModules_of_injective I
  SheafOfModules.isFlasque_toSheaf_of_injective X.ringCatSheaf I

end AlgebraicGeometry.Scheme.Modules
