import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenArrow

/-! # Affine basic-open coherent fixed-target arrow audit and direct client -/

open CategoryTheory AlgebraicGeometry

universe u

#print axioms AlgebraicGeometry.Coh.fixedTargetArrowExtension_pullbackBasicOpen

-- Import only the owner leaf and apply the theorem to an arbitrary arrow.
example {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (E : Coh (Spec R))
    (Z : Coh (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)))
    (β : Z ⟶ (Coh.pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj E) :
    ∃ (Y : Coh (Spec R)) (f : Y ⟶ E)
      (e : Z ≅ (Coh.pullback
        (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj Y),
      β = e.hom ≫ (Coh.pullback
        (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).map f := by
  exact Coh.fixedTargetArrowExtension_pullbackBasicOpen r E β
