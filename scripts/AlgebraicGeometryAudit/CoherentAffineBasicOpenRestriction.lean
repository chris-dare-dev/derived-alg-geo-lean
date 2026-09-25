import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenRestriction

/-! # SF11.4br chosen finite coherent subobject restriction audit and direct client -/

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

#print axioms AlgebraicGeometry.Coh.basicOpenChosenTildeSubobject
#print axioms AlgebraicGeometry.Coh.restrictBasicOpenSubobject
#print axioms AlgebraicGeometry.Coh.basicOpenSubobjectRawModule
#print axioms AlgebraicGeometry.Coh.basicOpenChosenTildeSubobject_restrict_rawModule

-- The direct owner-leaf import exposes the whole square, including the
-- coherent restriction and explicit raw-carrier map, without local instances.
example {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r s : R) (M : FGModuleCat.{u} R) (E : Coh (Spec R))
    (cR : E ≅ (FGModuleCat.affineTilde (R := R)).obj M)
    (N : Submodule R M.obj) (hN : N.FG) :
    let h : PrimeSpectrum.basicOpen (r * s) ≤ PrimeSpectrum.basicOpen r :=
      (PrimeSpectrum.basicOpen_mul r s).trans_le inf_le_left
    Coh.basicOpenSubobjectRawModule (r * s) M E cR
        (Coh.restrictBasicOpenSubobject r (r * s) h E
          (Coh.basicOpenChosenTildeSubobject r M E cR N hN)) =
      Submodule.span (Localization.Away (r * s))
        ((LocalizedModule.awayToAwayRightLinearMap (M := M.obj) r s) ''
          (Coh.basicOpenSubobjectRawModule r M E cR
            (Coh.basicOpenChosenTildeSubobject r M E cR N hN) :
              Set (LocalizedModule.Away r M.obj))) :=
  Coh.basicOpenChosenTildeSubobject_restrict_rawModule r s M E cR N hN
