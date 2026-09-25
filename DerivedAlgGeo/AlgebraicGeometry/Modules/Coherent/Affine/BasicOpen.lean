/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pullback
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Coherent pullback on an affine basic open

The coherent pullback along the open immersion `D(r) ↪ Spec R` agrees, up to a natural
isomorphism, with pullback along `Spec (Localization.Away r) → Spec R` followed by the
equivalence induced by `basicOpenIsoSpecAway r`. This is an ordinary, underived functor
comparison; it does not identify arbitrary ring localizations with open immersions.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Coh

/-- Restriction of coherent sheaves to `D(r)` is the affine localization-away pullback,
transported across `basicOpenIsoSpecAway r`. No Noetherian hypothesis is needed for this
comparison of ordinary pullback functors. -/
noncomputable def pullbackBasicOpenIsoSpecAway {R : CommRingCat.{u}} (r : R) :
    pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) ⋙
        pullback (basicOpenIsoSpecAway r).hom := by
  rw [← basicOpenIsoSpecAway_hom_SpecMap r]
  exact (pullbackComp (basicOpenIsoSpecAway r).hom
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).symm

end AlgebraicGeometry.Coh
