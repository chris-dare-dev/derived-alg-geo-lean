/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.AB
import DerivedAlgGeo.AlgebraicGeometry.Modules.Flasque
import DerivedAlgGeo.Topology.Sheaves.ModulesCohomology

/-!
# `Ext (𝒪_X, M)` in `X.Modules` is sheaf cohomology

`SheafOfModules.extUnitAddEquivDerivedH` for the wrapper `X.Modules` on a scheme. The
wrapper's category instance is a copy of that of `SheafOfModules X.ringCatSheaf`, so the
equivalence is reassembled from `extComparisonAddEquiv` in `X.Modules` rather than
transported: the degree-zero bijection is a statement about hom-sets, which the wrapper
shares on the nose, and acyclicity of injectives comes from
`Scheme.Modules.isFlasque_toSheaf_of_injective`.

`HasExt.{u + 1} X.Modules` is obtained from `HasDerivedCategory.standard`, the same route
as `AlgebraicGeometry/DerivedCategory/Dqc/Identification.lean`, so the `Ext` groups here are
the ones `CoherentExtComparison` is stated for.

## Main results

* `Scheme.Modules.unit`, `Scheme.Modules.unitFromConstant`.
* `Scheme.Modules.extUnitAddEquivDerivedH`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] HasDerivedCategory.standard CategoryTheory.hasExt_of_hasDerivedCategory

variable {X : Scheme.{u}}

variable (X) in
/-- The structure sheaf `𝒪_X` as an object of `X.Modules`. -/
noncomputable abbrev unit : X.Modules := SheafOfModules.unit X.ringCatSheaf

variable (X) in
/-- The map from the constant sheaf `ℤ` to the underlying abelian sheaf of `𝒪_X` sending
`1` to `1`. -/
noncomputable def unitFromConstant :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ (toSheaf X).obj (unit X) :=
  SheafOfModules.unitFromConstant X.ringCatSheaf isTerminalTop

/-- **Degree zero.** `f ↦ unitFromConstant ≫ toSheaf.map f` is a bijection from
`𝒪_X ⟶ M` to maps `ℤ ⟶ toSheaf M`. -/
theorem bijective_unitFromConstant_comp (M : X.Modules) :
    Function.Bijective (fun f : unit X ⟶ M ↦ unitFromConstant X ≫ (toSheaf X).map f) :=
  SheafOfModules.bijective_unitFromConstant_comp X.ringCatSheaf isTerminalTop M

variable [hExt : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- Injective `𝒪_X`-modules are acyclic for `Sheaf.H`. -/
theorem subsingleton_derivedH_toSheaf_of_injective (I : X.Modules) [Injective I] (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.derivedH hExt ((toSheaf X).obj I) (n + 1)) :=
  haveI := isFlasque_toSheaf_of_injective I
  TopCat.Sheaf.subsingleton_H_of_isFlasque (hExt := hExt) _ n

/-- **`Ext (𝒪_X, M)` is sheaf cohomology.** `Ext^n (𝒪_X) M ≃+ H^n (toSheaf M)` for every
`𝒪_X`-module `M`. -/
noncomputable def extUnitAddEquivDerivedH (M : X.Modules) (n : ℕ) :
    Ext.{u + 1} (unit X) M n ≃+ CategoryTheory.Sheaf.derivedH hExt ((toSheaf X).obj M) n :=
  extComparisonAddEquiv (R := toSheaf X) (unitFromConstant X)
    (fun M ↦ (bijective_extComparisonMap_zero_iff _ _).2 (bijective_unitFromConstant_comp M))
    (fun I _ n ↦ subsingleton_derivedH_toSheaf_of_injective I n) M n

end AlgebraicGeometry.Scheme.Modules
