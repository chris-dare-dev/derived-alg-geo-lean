/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenArrow

/-!
# Coherent subobjects on affine basic opens

A monomorphism into the pullback of a fixed coherent sheaf along `D(r) ↪ Spec R`
is, up to an isomorphism on its source, the pullback of an actual coherent
monomorphism into the fixed sheaf. The construction takes the image of the
underived fixed-target arrow witness. Exactness of open restriction identifies
that image after pullback.

This is a theorem for one affine basic open, not a gluing theorem for a
quasi-compact open in an arbitrary scheme.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Coh

/-- Every coherent subobject of the restriction of `E` to the actual basic open
`D(r)` lifts to a coherent subobject of `E`. In contrast to a
`FixedTargetMonoExtension` witness, the upstairs arrow `m` is itself monic. -/
theorem exists_mono_lift_pullbackBasicOpen
    {R : CommRingCat.{u}} [IsNoetherianRing R]
    (r : R) (E : Coh (Spec R))
    (Z : Coh (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)))
    (β : Z ⟶ (pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj E)
    [Mono β] :
    ∃ (L : Coh (Spec R)) (m : L ⟶ E), Mono m ∧
      ∃ (e : Z ≅ (pullback
        (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj L),
        β = e.hom ≫ (pullback
          (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).map m := by
  let j := Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)
  letI : PreservesFiniteLimits (Scheme.Modules.pullback j) :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback j)
  let F := pullback j
  have hsurj : Function.Surjective (Subobject.mapFunctor F (X := E)) :=
    Subobject.mapFunctor_surjective_of_fixedTargetArrowExtension
      F E (fixedTargetArrowExtension_pullbackBasicOpen r E)
  obtain ⟨P, hP⟩ := hsurj (Subobject.mk β)
  have hmk : Subobject.mk (F.map P.arrow) = Subobject.mk β := by
    simpa only [Subobject.mapFunctor_eq_mk_arrow] using hP
  let e := Subobject.isoOfMkEqMk β (F.map P.arrow) hmk.symm
  refine ⟨P, P.arrow, inferInstance, e, ?_⟩
  exact (Subobject.ofMkLEMk_comp hmk.symm.le).symm

end AlgebraicGeometry.Coh
