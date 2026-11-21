/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.OpenImmersion

/-!
# Local freeness on the range slice of an open immersion

Local generator data for the scheme-level restriction `M.restrict f` along an open immersion
`f : X ⟶ Y` transports to local generator data for the slice `M.over f.opensRange`, with the
same index types, and locally free data stays locally free data. This is the generating-sections
counterpart of `overQuasicoherentData`, and it is what lets local freeness of a fixed rank be
tested on the restrictions of a sheaf to the members of an open cover.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.overLocalGeneratorsData`: local generator data on the range
  slice from local generator data on the restriction.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isLocallyFreeOfRank_over_of_restrict`: local freeness of rank `r`
  of the restriction implies it for the range slice.

## Implementation notes

The cover of the restriction lives on `X.Opens` and has to be moved to the slice over
`f.opensRange`. The round trip through `opensRangeEquivalence` is an equality of opens, not
merely an isomorphism, and `generatingSectionsOverOfEq` discharges it once by `subst`, as
`presentationOverOfEq` does for presentations.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Generating sections of the scheme-level restriction over `U` transport to generating
sections of the range-slice restriction over `W`, given that `W` maps to `U` under the site
equivalence. -/
noncomputable def generatingSectionsOverOfEq (M : Y.Modules) (W : Over f.opensRange) (U : X.Opens)
    (h : f.opensRangeEquivalence.functor.obj W = U)
    (σ : ((M.restrict f).over U).GeneratingSections) :
    ((M.over f.opensRange).over W).GeneratingSections := by
  subst h
  exact (σ.map (f.opensRangeOverModulesEquivalence W).functor
      (f.opensRangeOverModulesEquivalenceUnitIso W).symm).ofEpi
    (f.restrictOverIsoForward M W).hom

/-- The transported generating sections have the original index type. -/
lemma generatingSectionsOverOfEq_I (M : Y.Modules) (W : Over f.opensRange) (U : X.Opens)
    (h : f.opensRangeEquivalence.functor.obj W = U)
    (σ : ((M.restrict f).over U).GeneratingSections) :
    (f.generatingSectionsOverOfEq M W U h σ).I = σ.I := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The transported generating sections of a free basis are again a free basis. -/
lemma isIso_generatingSectionsOverOfEq_π (M : Y.Modules) (W : Over f.opensRange) (U : X.Opens)
    (h : f.opensRangeEquivalence.functor.obj W = U)
    (σ : ((M.restrict f).over U).GeneratingSections) [IsIso σ.π] :
    IsIso (f.generatingSectionsOverOfEq M W U h σ).π := by
  subst h
  exact SheafOfModules.GeneratingSections.isIso_ofEpi_π _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Local generator data for the scheme-level restriction along an open immersion transports to
local generator data for the range slice, with the same index types. -/
noncomputable def overLocalGeneratorsData (M : Y.Modules)
    (q : SheafOfModules.LocalGeneratorsData.{u}
      (show SheafOfModules X.ringCatSheaf from M.restrict f)) :
    SheafOfModules.LocalGeneratorsData.{u} (M.over f.opensRange) where
  I := q.I
  X i := f.opensRangeEquivalence.inverse.obj (q.X i)
  coversTop := GrothendieckTopology.CoversTop.map_equivalence q.coversTop
    f.opensRangeEquivalence.symm f.opensRangeEquivalence_inverse_coverPreserving
  generators i :=
    f.generatingSectionsOverOfEq M _ (q.X i) (f.preimage_image_eq (q.X i)) (q.generators i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Locally free data on the restriction transports to locally free data on the range slice. -/
instance isLocallyFreeData_overLocalGeneratorsData (M : Y.Modules)
    (q : SheafOfModules.LocalGeneratorsData.{u}
      (show SheafOfModules X.ringCatSheaf from M.restrict f))
    [q.IsLocallyFreeData] : (f.overLocalGeneratorsData M q).IsLocallyFreeData where
  isIso i := by
    change q.I at i
    have : IsIso (q.generators i).π :=
      SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso i
    exact f.isIso_generatingSectionsOverOfEq_π M _ (q.X i) _ (q.generators i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Local freeness of a fixed rank of the scheme-level restriction along an open immersion
implies it for the range slice: the transported frame has the same index types. -/
theorem isLocallyFreeOfRank_over_of_restrict (M : Y.Modules) {r : ℕ}
    (h : SheafOfModules.IsLocallyFreeOfRank.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M.restrict f) r) :
    SheafOfModules.IsLocallyFreeOfRank.{u, u, u} (M.over f.opensRange) r := by
  obtain ⟨q, hq, hrank⟩ := h
  have : q.IsLocallyFreeData := hq
  refine ⟨f.overLocalGeneratorsData M q, isLocallyFreeData_overLocalGeneratorsData f M q,
    fun i ↦ ?_⟩
  exact (congrArg Nat.card (f.generatingSectionsOverOfEq_I M _ (q.X i) _ (q.generators i))).trans
    (hrank i)

end AlgebraicGeometry.Scheme.Hom
