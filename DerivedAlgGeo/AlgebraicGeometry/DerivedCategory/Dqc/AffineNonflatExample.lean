/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RingHom.Flat
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineGeometricCorePseudofunctor

/-!
# A supported non-flat affine derived pullback

This file supplies the concrete example required by SF8.5 item 9.  The ring
map `ℤ → ZMod 2` is a non-isomorphism and is not flat, while the existing
geometric affine bounded-above-projective core pseudofunctor constructs its
pullback without a flatness hypothesis.

This is deliberately an example, not an existence theorem for arbitrary
scheme-module resolutions.  It consumes the supported affine
K-projective-derived lane already constructed in
`AffineGeometricCorePseudofunctor.lean`; it does not identify that lane with
the full relative-perfect locus or prove the general-scheme preservation
theorems still listed in #554.

`AffineNonflatDerivedObject.lean` separately computes the degree-minus-one
effect of this particular map on an explicit two-term free representative.
That calculation remains in the same affine bounded-projective lane and does
not enlarge this example into a scheme-level assertion.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc

open AlgebraicGeometry CategoryTheory

noncomputable section

/-- The target ring in the standard closed-immersion example. -/
abbrev zmodTwoRing : CommRingCat :=
  CommRingCat.of (ZMod 2)

/-- The nonidentity ring morphism `ℤ → ZMod 2`. -/
def zmodTwoRingMap : CommRingCat.of ℤ ⟶ zmodTwoRing :=
  CommRingCat.ofHom (Int.castRingHom (ZMod 2))

/-- The corresponding morphism of affine schemes. -/
def zmodTwoSchemeMap :
    Spec zmodTwoRing ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map zmodTwoRingMap

/-- The closed-immersion ring map is not flat.

Flatness would make the `ℤ`-module `ZMod 2` torsion-free, but `2 • 1 = 0`
while both the scalar `2` and the element `1` are nonzero. -/
theorem zmodTwoRingMap_not_flat :
    ¬ zmodTwoRingMap.hom.Flat := by
  change ¬ (Int.castRingHom (ZMod 2)).Flat
  intro h
  letI : Algebra ℤ (ZMod 2) := (Int.castRingHom (ZMod 2)).toAlgebra
  letI : Module ℤ (ZMod 2) := Algebra.toModule
  have hf : Module.Flat ℤ (ZMod 2) := by
    simpa only [RingHom.Flat] using h
  letI : Module.Flat ℤ (ZMod 2) := hf
  have ht : Module.IsTorsionFree ℤ (ZMod 2) := inferInstance
  have hzero : (2 : ℤ) • (1 : ZMod 2) = 0 := by
    change (2 : ZMod 2) = 0
    exact ZMod.natCast_self 2
  have hcases := (Module.isTorsionFree_iff_smul_eq_zero.mp ht) 2 1 hzero
  rcases hcases with h2 | h1
  · norm_num at h2
  · norm_num at h1

/-- The corresponding affine-scheme morphism is not flat. -/
theorem zmodTwoSchemeMap_not_flat :
    ¬ AlgebraicGeometry.Flat zmodTwoSchemeMap := by
  change ¬ AlgebraicGeometry.Flat (Spec.map zmodTwoRingMap)
  rw [AlgebraicGeometry.Flat.SpecMap_iff]
  exact zmodTwoRingMap_not_flat

/-- The example is genuinely nonidentity: its ring map is not an isomorphism. -/
theorem zmodTwoRingMap_not_iso : ¬ IsIso zmodTwoRingMap := by
  rw [ConcreteCategory.isIso_iff_bijective]
  intro h
  have hinj : Function.Injective (Int.castRingHom (ZMod 2)) := h.1
  apply (by norm_num : (0 : ℤ) ≠ 2)
  apply hinj
  change (0 : ZMod 2) = 2
  exact (ZMod.natCast_self 2).symm

/-- The actual supported affine derived pullback along the non-flat example.

The source and target are the already-defined geometric affine moduli fibers;
the construction therefore has no caller-supplied flatness or exactness
hypothesis. -/
def zmodTwoAffinePullback :
    AffineBoundedAboveProjectiveModuliFiber (CommRingCat.of ℤ) ⥤
      AffineBoundedAboveProjectiveModuliFiber zmodTwoRing :=
  affineGeometricBoundedAboveProjectiveCorePullback zmodTwoRingMap

end

end AlgebraicGeometry.DerivedCategory.Dqc
