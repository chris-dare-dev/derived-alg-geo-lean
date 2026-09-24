import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Localization

/-! # Affine coherent fixed-target arrow audit and direct client -/

open CategoryTheory

universe u

#print axioms AlgebraicGeometry.Coh.fixedTargetArrowExtension_pullbackSpecMap_of_isLocalization

-- Import only the owner leaf and use its public theorem on an arbitrary arrow.
example {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] (S : Submonoid R) [IsLocalization S A]
    (E : AlgebraicGeometry.Coh (AlgebraicGeometry.Spec (CommRingCat.of R)))
    (Z : AlgebraicGeometry.Coh (AlgebraicGeometry.Spec (CommRingCat.of A)))
    (β : Z ⟶ (AlgebraicGeometry.Coh.pullback
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj E) :
    ∃ (Y : AlgebraicGeometry.Coh (AlgebraicGeometry.Spec (CommRingCat.of R)))
      (f : Y ⟶ E)
      (e : Z ≅ (AlgebraicGeometry.Coh.pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj Y),
      β = e.hom ≫ (AlgebraicGeometry.Coh.pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A)))).map f := by
  exact AlgebraicGeometry.Coh.fixedTargetArrowExtension_pullbackSpecMap_of_isLocalization
    S E β
