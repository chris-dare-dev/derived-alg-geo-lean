/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum
import DerivedAlgGeo.RingTheory.Spectrum.Prime.CoversTop

/-!
# Affine and projective spectrum API probe

This compile-only probe checks the pinned Mathlib APIs for prime and scheme
spectra, affine module sheaves, and projective affine charts, together with the
repository's concrete comparison maps. It adds no mathematical declarations.
`DerivedAlgGeo.Development` imports this module so the verification sweep and
emitter cover the probe; the stable `DerivedAlgGeo` root does not import it.

The general localization criterion for the affine counit is Mathlib's
`AlgebraicGeometry.IsLocalizing` and
`AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing`. The local predicate
using `basicOpenRestriction` is definitionally the same, checked below by
`Iff.rfl`.

## Main definitions

This verification module introduces no public definitions.

## Main results

The anonymous example checks that Mathlib's `AlgebraicGeometry.IsLocalizing`
condition is definitionally equal to the condition expressed using
`AlgebraicGeometry.Scheme.Modules.basicOpenRestriction`.

## Implementation notes

The declaration checks verify the names and types cited by the affine and
projective spectrum placement map. The anonymous example uses `Iff.rfl` so a
change that breaks the definitional agreement fails compilation.
`DerivedAlgGeo.Development` imports this module so the verification sweep and
emitter cover it; the stable `DerivedAlgGeo` root does not import it.

## References

- Mathlib v4.32.1, pinned at commit
  `520045ab14e26149ee970e2e617ca04b09bde5d6`:
  `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`.
- Issue #1608.

## Tags

affine schemes, projective spectra, localization, API verification
-/

#check @PrimeSpectrum
#check @PrimeSpectrum.basicOpen
#check @PrimeSpectrum.iSup_basicOpen_eq_top_iff
#check @PrimeSpectrum.isBasis_basic_opens
#check @PrimeSpectrum.coversTop_basicOpen_of_span_eq_top

#check @AlgebraicGeometry.Spec
#check @AlgebraicGeometry.Spec.topObj
#check @AlgebraicGeometry.Spec.topObj_forget
#check @AlgebraicGeometry.Spec.toLocallyRingedSpace
#check @AlgebraicGeometry.Scheme.Spec
#check @AlgebraicGeometry.ΓSpec.adjunction
#check @AlgebraicGeometry.AffineScheme.equivCommRingCat
#check @AlgebraicGeometry.IsLocalizing
#check @AlgebraicGeometry.modulesSpecToSheaf
#check @AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing
#check @AlgebraicGeometry.tildeEquiv
#check @AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent

#check @AlgebraicGeometry.Proj
#check @AlgebraicGeometry.Proj.basicOpen
#check @AlgebraicGeometry.Proj.basicOpenIsoSpec
#check @AlgebraicGeometry.Proj.awayι
#check @AlgebraicGeometry.Proj.affineOpenCover
#check @AlgebraicGeometry.Proj.toSpecZero
#check @AlgebraicGeometry.Proj.awayι_toSpecZero
#check @HomogeneousLocalization.Away
#check @Localization.Away
#check @CommRingCat
#check @CommRingCat.of
#check @AlgebraicGeometry.Proj.chartRing
#check @AlgebraicGeometry.Proj.awayRestrict

#check @AlgebraicGeometry.Scheme.Modules.basicOpenRestriction
#check @AlgebraicGeometry.Scheme.Modules.fromTildeΓ
#check @AlgebraicGeometry.Scheme.Modules.exists_basicOpen_presentation_cover_of_quasicoherentData
#check @AlgebraicGeometry.Scheme.Modules.exists_basicOpen_presentation_cover
#check @AlgebraicGeometry.isIso_fromTildeΓ_app_basicOpen
#check @AlgebraicGeometry.isIso_fromTildeΓ_of_isLocalizedModule
#check @AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_iff_isLocalizedModule
#check @AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_tilde
#check @AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isIso
#check @AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_presentation
#check @AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent
#check @AlgebraicGeometry.Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen
#check @AlgebraicGeometry.Scheme.Modules.toOpen_fromTildeΓ_app
#check @AlgebraicGeometry.isIso_fromTildeΓ_of_presentation
#check @AlgebraicGeometry.tilde
#check @AlgebraicGeometry.tilde.toOpen
#check @AlgebraicGeometry.tilde.toOpen_res
#check @CategoryTheory.NatIso.isIso_app_of_isIso
#check @CategoryTheory.IsIso
#check @TopCat.Sheaf.restrictHomEquivHom
#check @IsLocalizedModule.lift
#check @Submonoid.powers
#check @IsLocalizedModule

example {R : CommRingCat} (M : (AlgebraicGeometry.Spec R).Modules) :
    AlgebraicGeometry.IsLocalizing (AlgebraicGeometry.modulesSpecToSheaf.obj M) ↔
      ∀ f : R, IsLocalizedModule (Submonoid.powers f)
        (M.basicOpenRestriction f).hom := Iff.rfl
