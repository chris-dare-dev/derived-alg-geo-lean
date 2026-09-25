import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpen

/-! # Affine basic-open coherent pullback comparison audit and direct client -/

open CategoryTheory AlgebraicGeometry

universe u

#print axioms AlgebraicGeometry.Coh.pullbackBasicOpenIsoSpecAway

-- Import only the owner leaf and use the comparison on an arbitrary coherent sheaf.
noncomputable example {R : CommRingCat.{u}} (r : R) (E : Coh (Spec R)) :
    (Coh.pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj E ≅
      (Coh.pullback (basicOpenIsoSpecAway r).hom).obj
        ((Coh.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj E) :=
  (Coh.pullbackBasicOpenIsoSpecAway r).app E

-- The scheme isomorphism supplies the inverse coherent-pullback functor as an equivalence.
noncomputable example {R : CommRingCat.{u}} (r : R) :
    Coh (Spec (CommRingCat.of (Localization.Away r))) ≌
      Coh (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)) :=
  Coh.pullbackEquivalence (basicOpenIsoSpecAway r)
