/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Cohomology
import DerivedAlgGeo.Topology.Sheaves.Flasque

/-!
# `Ext` from the unit module sheaf on a space computes sheaf cohomology

On a topological space the acyclicity hypothesis of `SheafOfModules.extUnitAddEquivH` holds
unconditionally: injective sheaves of modules are flasque
(`SheafOfModules.isFlasque_toSheaf_of_injective`) and flasque sheaves are acyclic
(`TopCat.Sheaf.subsingleton_H_of_isFlasque`). So `Ext^n (unit R) M ≃+ H^n (M)` for every
sheaf of `R`-modules `M` on a space, Hartshorne III.2.6.

The `HasExt` instance on abelian sheaves is passed explicitly, as in
`Topology/Sheaves/Cech/BasisComparison.lean`, and the cohomology is `Sheaf.derivedH`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace SheafOfModules

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [hExt : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- Injective sheaves of modules on a space are acyclic for `Sheaf.H`. -/
theorem subsingleton_derivedH_toSheaf_of_injective (I : SheafOfModules.{u} R) [Injective I]
    (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.derivedH hExt ((toSheaf R).obj I) (n + 1)) :=
  haveI := isFlasque_toSheaf_of_injective R I
  TopCat.Sheaf.subsingleton_H_of_isFlasque (hExt := hExt) _ n

variable [hExtM : HasExt.{u + 1} (SheafOfModules.{u} R)]

/-- **`Ext` from the unit computes sheaf cohomology on a space.**
`Ext^n (unit R) M ≃+ H^n (toSheaf M)` for every sheaf of `R`-modules `M`. -/
noncomputable def extUnitAddEquivDerivedH (M : SheafOfModules.{u} R) (n : ℕ) :
    Ext.{u + 1} (unit R) M n ≃+ CategoryTheory.Sheaf.derivedH hExt ((toSheaf R).obj M) n :=
  extUnitAddEquivH (hExtM := hExtM) (hExtA := hExt) R isTerminalTop
    (fun I _ n ↦ subsingleton_derivedH_toSheaf_of_injective R I n) M n

end SheafOfModules
