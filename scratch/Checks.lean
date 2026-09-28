import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum
import DerivedAlgGeo.RingTheory.Spectrum.Prime.CoversTop

-- This file is a reviewable API probe for issue #1608, not a library module.

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
