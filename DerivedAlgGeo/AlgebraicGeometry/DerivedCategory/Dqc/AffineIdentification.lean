/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.AcyclicGenerators
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.AffineVanishing
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.UnitExt
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.Identification
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Free
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# The bounded-coherent identification on affine noetherian schemes

This file proves `CoherentExtComparison (Spec R)` for a noetherian ring `R`, hence
`HasBoundedCoherentDqcIdentification (Spec R)` through `Dqc/Identification.lean`.

## Main definitions

This file introduces no new definitions; it proves facts about
`AlgebraicGeometry.DerivedCategory.Dqc.CoherentExtComparison` and
`AlgebraicGeometry.DerivedCategory.Dqc.HasBoundedCoherentDqcIdentification`.

## Main results

* `AlgebraicGeometry.DerivedCategory.Dqc.subsingleton_ext_ι_affineFree` — higher
  `Ext` out of a free sheaf `𝒪^k` into a coherent sheaf vanishes in all module
  sheaves on `Spec R`.
* `AlgebraicGeometry.DerivedCategory.Dqc.coherentExtComparison_spec` — the coherent
  `Ext` comparison holds on `Spec R`.
* `AlgebraicGeometry.DerivedCategory.Dqc.hasBoundedCoherentDqcIdentification_spec` —
  the bounded-coherent identification holds on `Spec R`.

## Implementation notes

The `Ext` comparison is `Functor.bijective_mapExtAddHom_of_generators` applied to
`Coh.ι (Spec R)` with the free sheaves `𝒪^k` as generators:

* every coherent sheaf is a quotient of some `𝒪^k` (`Coh.exists_affineFree_epi`);
* `Ext^(n+1) (𝒪^k, G)` vanishes in `Coh (Spec R)` because `𝒪^k` is projective there
  (`Coh.projective_affineFree`);
* `Ext^(n+1) (𝒪^k, G)` vanishes in all module sheaves because it is `H^(n+1)(G)^k`
  (`Scheme.Modules.extUnitAddEquivDerivedH`, `Ext.subsingleton_biproduct_left`) and
  quasi-coherent sheaves on an affine scheme have no higher cohomology
  (`modules_H_subsingleton_of_isQuasicoherent`);
* `Coh.ι` is fully faithful, so bijective on `Ext⁰`.

The comparison for a general locally noetherian scheme is not proved here.

## References

The repository's `Functor.bijective_mapExtAddHom_of_generators`,
`Scheme.Modules.extUnitAddEquivDerivedH` and
`Cohomology.modules_H_subsingleton_of_isQuasicoherent`, and Mathlib's
`Ext.eq_zero_of_projective`.

## Tags

bounded derived category, coherent sheaves, affine scheme, Ext comparison
-/

universe u

open CategoryTheory CategoryTheory.Limits Abelian

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.hasExt_of_hasDerivedCategory

namespace AlgebraicGeometry.DerivedCategory.Dqc

attribute [local instance] Coh.ι_additive Coh.ι_preservesFiniteLimits
  Coh.ι_preservesFiniteColimits Abelian.hasFiniteBiproducts

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- `Ext^(n+1) (𝒪^k, G)` in all module sheaves vanishes for coherent `G` on `Spec R`: it is
`H^(n+1)(G)^k`, and quasi-coherent sheaves on an affine scheme have no higher cohomology. -/
theorem subsingleton_ext_ι_affineFree (k : ℕ) (Y : Coh (Spec R)) (n : ℕ) :
    Subsingleton (Ext.{u + 1} ((Coh.ι (Spec R)).obj (Coh.affineFree k))
      ((Coh.ι (Spec R)).obj Y) (n + 1)) := by
  haveI : Y.obj.IsFinitePresentation := Y.property
  have h : ∀ _ : Fin k, Subsingleton (Ext.{u + 1} ((tilde.functor R).obj (ModuleCat.of R R))
      ((Coh.ι (Spec R)).obj Y) (n + 1)) := fun _ ↦ by
    haveI := Cohomology.modules_H_subsingleton_of_isQuasicoherent Y.obj (n + 1) (Nat.succ_pos n)
    exact (Scheme.Modules.extUnitAddEquivDerivedH Y.obj (n + 1)).toEquiv.subsingleton
  exact Ext.subsingleton_of_iso_left (Coh.ιAffineFreeIso k) (n + 1)
    (Ext.subsingleton_biproduct_left _ _ _ h)

/-- **The coherent `Ext` comparison holds on affine noetherian schemes.** -/
theorem coherentExtComparison_spec : CoherentExtComparison (Spec R) := fun F G n ↦
  (Coh.ι (Spec R)).bijective_mapExtAddHom_of_generators (fun P ↦ ∃ k, P = Coh.affineFree k)
    Coh.exists_affineFree_epi
    (fun P hP Y n ↦ by
      obtain ⟨k, rfl⟩ := hP
      haveI := Coh.projective_affineFree (R := R) k
      exact subsingleton_of_forall_eq 0 fun e ↦ Ext.eq_zero_of_projective e)
    (fun P hP Y n ↦ by
      obtain ⟨k, rfl⟩ := hP
      exact subsingleton_ext_ι_affineFree k Y n)
    (Coh.ι (Spec R)).bijective_mapExtAddHom_zero n F G

/-- **The bounded-coherent identification holds on affine noetherian schemes.** -/
theorem hasBoundedCoherentDqcIdentification_spec :
    HasBoundedCoherentDqcIdentification (Spec R) :=
  hasBoundedCoherentDqcIdentification_of_coherentExtComparison coherentExtComparison_spec

end AlgebraicGeometry.DerivedCategory.Dqc
