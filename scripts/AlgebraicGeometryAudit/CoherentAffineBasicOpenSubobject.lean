import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenSubobject

/-! # Affine basic-open coherent mono-lift audit and direct client -/

open CategoryTheory AlgebraicGeometry

universe u

#print axioms AlgebraicGeometry.Coh.exists_mono_lift_pullbackBasicOpen

-- Import only the owner leaf and lift an arbitrary mono into a fixed coherent target.
example {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (E : Coh (Spec R))
    (Z : Coh (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)))
    (β : Z ⟶ (Coh.pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj E)
    [Mono β] :
    ∃ (L : Coh (Spec R)) (m : L ⟶ E), Mono m ∧
      ∃ (e : Z ≅ (Coh.pullback
        (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj L),
        β = e.hom ≫ (Coh.pullback
          (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).map m := by
  exact Coh.exists_mono_lift_pullbackBasicOpen r E Z β
