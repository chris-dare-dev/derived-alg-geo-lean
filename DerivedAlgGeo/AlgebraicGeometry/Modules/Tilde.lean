/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Module

/-!
# The range of a tilde map on an affine basic open

On `D(r)`, the range of the map of tilde sheaves induced by a module map is the
localization of its range. The statement uses the canonical
`Localization.Away r`-action transported to the underlying `R`-module of
sections by `IsLocalizedModule.module`. It does not identify that action
definitionally with the structure-sheaf action, nor compare categorical
coherent subobjects or glue them across opens.
-/

open CategoryTheory Opposite _root_.PrimeSpectrum

universe u

namespace AlgebraicGeometry.tilde

variable (R : CommRingCat.{u}) (K M : ModuleCat.{u} R) (g : K ⟶ M) (r : R)

/-- The range of `tilde.map g` on `D(r)` is the localization away from `r` of
`g`'s range. The result applies to an inclusion `N.subtype` as well as an
arbitrary module map. Both localized-module structures and scalar towers are
proof-local; no global instance for the section modules is introduced. -/
theorem localized'_range_eq_range_map_basicOpen :
    let S := Submonoid.powers r
    let U := basicOpen r
    let fK := (toOpen K U).hom
    let fM := (toOpen M U).hom
    letI : IsLocalizedModule S fK := by
      exact inferInstanceAs (IsLocalizedModule.Away r (toOpen K (basicOpen r)).hom)
    letI : IsLocalizedModule S fM := by
      exact inferInstanceAs (IsLocalizedModule.Away r (toOpen M (basicOpen r)).hom)
    letI : Module (Localization.Away r) _ := IsLocalizedModule.module S fK
    letI : IsScalarTower R (Localization.Away r) _ :=
      IsLocalizedModule.isScalarTower_module S fK
    letI : Module (Localization.Away r) _ := IsLocalizedModule.module S fM
    letI : IsScalarTower R (Localization.Away r) _ :=
      IsLocalizedModule.isScalarTower_module S fM
    let h := ((modulesSpecToSheaf.map (tilde.map g)).hom.app (op U)).hom
    g.hom.range.localized' (Localization.Away r) S fM =
      (h.extendScalarsOfIsLocalization S (Localization.Away r)).range := by
  let S := Submonoid.powers r
  let U := basicOpen r
  let fK := (toOpen K U).hom
  let fM := (toOpen M U).hom
  letI : IsLocalizedModule S fK := by
    exact inferInstanceAs (IsLocalizedModule.Away r (toOpen K (basicOpen r)).hom)
  letI : IsLocalizedModule S fM := by
    exact inferInstanceAs (IsLocalizedModule.Away r (toOpen M (basicOpen r)).hom)
  letI : Module (Localization.Away r) _ := IsLocalizedModule.module S fK
  letI : IsScalarTower R (Localization.Away r) _ :=
    IsLocalizedModule.isScalarTower_module S fK
  letI : Module (Localization.Away r) _ := IsLocalizedModule.module S fM
  letI : IsScalarTower R (Localization.Away r) _ :=
    IsLocalizedModule.isScalarTower_module S fM
  let h := ((modulesSpecToSheaf.map (tilde.map g)).hom.app (op U)).hom
  have hmap : h = (IsLocalizedModule.map S fK fM) g.hom := by
    apply IsLocalizedModule.linearMap_ext S fK fM
    apply LinearMap.ext
    intro x
    change h (fK x) = (IsLocalizedModule.map S fK fM g.hom) (fK x)
    calc
      h (fK x) = fM (g.hom x) := by
        have hsq := toOpen_map_app g U
        exact congrArg (fun q => q.hom x) hsq
      _ = _ := (IsLocalizedModule.map_apply S fK fM g.hom x).symm
  change g.hom.range.localized' (Localization.Away r) S fM =
    (h.extendScalarsOfIsLocalization S (Localization.Away r)).range
  rw [hmap]
  exact LinearMap.localized'_range_eq_range_localizedMap
    (Localization.Away r) S fK fM g.hom

end AlgebraicGeometry.tilde
