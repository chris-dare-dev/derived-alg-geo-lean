import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.AffineCoherentLocalizationComparison

/-! Audit and direct naturality client for exact affine coherent derived pullback. -/

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.finiteAffineTildeDerived
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.coherentLocalizationDerivedPullback
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.finiteExtendScalarsDerived
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.affineCoherentLocalizationDerivedComparison

noncomputable section

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [IsNoetherianRing R] (S : Submonoid R) [IsLocalization S A]

-- The exported square applies directly to an arbitrary derived arrow, with
-- naturality supplied by the natural isomorphism itself.
example (X Y : _root_.DerivedCategory (FGModuleCat.{u} R)) (g : X ⟶ Y) :
    letI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
    let E := AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.affineCoherentLocalizationDerivedComparison
      (R := R) (A := A) S
    (AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.finiteAffineTildeDerived
      (CommRingCat.of R) ⋙
      AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.coherentLocalizationDerivedPullback
        (R := R) (A := A) S).map g ≫ E.hom.app Y =
      E.hom.app X ≫
      (AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.finiteExtendScalarsDerived
        (R := R) (A := A) S ⋙
        AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.finiteAffineTildeDerived
          (CommRingCat.of A)).map g := by
  letI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
  exact (AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.affineCoherentLocalizationDerivedComparison
    (R := R) (A := A) S).hom.naturality g

end
