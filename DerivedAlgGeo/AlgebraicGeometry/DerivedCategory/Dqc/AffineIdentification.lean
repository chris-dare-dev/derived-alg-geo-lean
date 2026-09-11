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

`CoherentExtComparison (Spec R)` for a noetherian ring `R`, hence
`HasBoundedCoherentDqcIdentification (Spec R)` through `Dqc/Identification.lean`.

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

This is the first scheme marked as satisfying `CoherentExtComparison`. The general case
remains open; see `docs/architecture/cutover-ledger.md`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Abelian

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.hasExt_of_hasDerivedCategory

namespace AlgebraicGeometry.DerivedCategory.Dqc

attribute [local instance] Coh.ι_additive Coh.ι_preservesFiniteLimits
  Coh.ι_preservesFiniteColimits Abelian.hasFiniteBiproducts

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

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
