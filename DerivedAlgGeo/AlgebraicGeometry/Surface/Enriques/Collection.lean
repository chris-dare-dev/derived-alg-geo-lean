/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.IntersectionTheory.Surface.Number
import DerivedAlgGeo.AlgebraicGeometry.Surface.Enriques.Basic
import DerivedAlgGeo.LinearAlgebra.Lattice.IsotropicSequence

/-!
# Isotropic 10-collections on an Enriques surface

Li--Nuer--Stellari--Zhao, arXiv:1912.04332v2, Definition 3.2 and equation (3.2), attach to a
Fano polarization `Δ` an isotropic 10-sequence of numerical classes `fᵢ` satisfying

`3δ = f₁ + ⋯ + f₁₀`.

This file records line-bundle lifts of those classes against a supplied surface intersection
context.  The repository has no geometric `Num(Y)` quotient, nef predicate, or ampleness API.
Consequently the numerical equality is supplied in its intrinsic intersection-theoretic form:
`3δ` and `∑ fᵢ` have equal intersection with every Picard class.  The field does not claim that
the chosen Picard lift is nef or ample, and no collection is constructed on a concrete surface.

The two arithmetic consequences used by the Torelli lane are proved rather than stored:
`Δ · Fᵢ = 3` and `Δ² = 10`.  In particular, the stale value `Δ · Fᵢ = 1` is not compatible
with equation (3.2): the sum of the other nine isotropic classes pairs to `9`.

## Main definitions

* `IsotropicCollection` -- ten line bundles, a Fano-class lift, an intersection context, the
  isotropic equations, and the numerical normalization.
* `IsotropicCollection.classes` and `sumClass` -- the additive Picard classes consumed by the
  lattice API.

## Main results

* `IsotropicCollection.isIsotropicSequence` -- the geometric fields packaged at the generic
  lattice root.
* `IsotropicCollection.bundleClass_ne` -- distinct indices give distinct Picard classes.
* `IsotropicCollection.fano_intersection_bundle` -- `Δ · Fᵢ = 3`.
* `IsotropicCollection.fano_self_intersection` -- `Δ² = 10`.
-/

open CategoryTheory
open scoped BigOperators

universe u

namespace AlgebraicGeometry.EnriquesSurface

open IntersectionTheory.Number
open Scheme.Modules

variable {k : Type u} [Field k]
variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k Y]
variable {C : SmoothProperVariety.CanonicalSheafData k Y 2}
  [SmoothProperVariety.IsEnriquesSurface k Y C]
variable {D : Cohomology.FiniteCohomology k Y} {S : D.LinearConnectingSystem}

/-- Supplied geometric data for an isotropic 10-collection of line bundles.

The normalization is equation (3.2) of arXiv:1912.04332v2, expressed through all intersection
probes because the repository does not yet construct `Num(Y)`.  `fano` is only a Picard lift of
the numerical Fano class: nefness and ampleness are deliberately not asserted. -/
structure IsotropicCollection
    {C : SmoothProperVariety.CanonicalSheafData k Y 2}
    [SmoothProperVariety.IsEnriquesSurface k Y C]
    (D : Cohomology.FiniteCohomology k Y) (S : D.LinearConnectingSystem) where
  /-- The ten line-bundle lifts `O_Y(Fᵢ)`. -/
  bundles : Fin 10 → LineBundleData Y
  /-- A line-bundle lift of the numerical class of the Fano polarization. -/
  fano : LineBundleData Y
  /-- The supplied Snapper context in which all numerical equations are evaluated. -/
  intersection : IntersectionContext D S 2
  /-- Each selected class is isotropic. -/
  self_isotropic : ∀ i,
    intersection.picardIntersectionNumber ![(bundles i).toPic, (bundles i).toPic] = 0
  /-- Distinct selected classes have intersection one. -/
  pairwise_one : ∀ i j, i ≠ j →
    intersection.picardIntersectionNumber ![(bundles i).toPic, (bundles j).toPic] = 1
  /-- Equation (3.2), `3δ = ∑ fᵢ`, as numerical equivalence: both sides pair equally
  with every Picard class.  This is supplied data because no `Num(Y)` quotient exists at the
  current pin. -/
  fano_normalization : ∀ L : Pic Y,
    intersection.surfaceIntersectionPairing
        ((3 : ℤ) • Additive.ofMul fano.toPic) (Additive.ofMul L) =
      intersection.surfaceIntersectionPairing
        (∑ i, Additive.ofMul (bundles i).toPic) (Additive.ofMul L)

namespace IsotropicCollection

variable (T : IsotropicCollection (Y := Y) (C := C) D S)

/-- The ten additive Picard classes underlying the selected line bundles. -/
noncomputable def classes : Fin 10 → Additive (Pic Y) :=
  fun i ↦ Additive.ofMul (T.bundles i).toPic

/-- The sum `∑ fᵢ` of the ten selected additive Picard classes. -/
noncomputable def sumClass : Additive (Pic Y) :=
  ∑ i, T.classes i

/-- The additive Picard lift of the Fano class. -/
noncomputable def fanoClass : Additive (Pic Y) :=
  Additive.ofMul T.fano.toPic

/-- The geometric intersection equations package into the generic integral-lattice notion of an
isotropic sequence. -/
theorem isIsotropicSequence :
    IntegralLattice.IsIsotropicSequence T.intersection.surfaceIntersectionPairing T.classes := by
  constructor
  · intro i
    change T.intersection.surfaceIntersectionPairing
      (Additive.ofMul (T.bundles i).toPic) (Additive.ofMul (T.bundles i).toPic) = 0
    rw [IntersectionContext.surfaceIntersectionPairing_apply,
      ← IntersectionContext.picardIntersectionNumber_fin2]
    exact T.self_isotropic i
  · intro i j hij
    change T.intersection.surfaceIntersectionPairing
      (Additive.ofMul (T.bundles i).toPic) (Additive.ofMul (T.bundles j).toPic) = 1
    rw [IntersectionContext.surfaceIntersectionPairing_apply,
      ← IntersectionContext.picardIntersectionNumber_fin2]
    exact T.pairwise_one i j hij

/-- Distinct members of an isotropic collection determine distinct Picard classes. -/
theorem bundleClass_ne {i j : Fin 10} (hij : i ≠ j) :
    (T.bundles i).toPic ≠ (T.bundles j).toPic := by
  intro heq
  have hpair := T.pairwise_one i j hij
  have hself := T.self_isotropic i
  have hcongr :
      T.intersection.picardIntersectionNumber
          ![(T.bundles i).toPic, (T.bundles j).toPic] =
        T.intersection.picardIntersectionNumber
          ![(T.bundles i).toPic, (T.bundles i).toPic] := by
    apply T.intersection.picardIntersectionNumber_congr
    intro a
    fin_cases a
    · rfl
    · exact heq.symm
  omega

/-- The normalization forces `Δ · Fᵢ = 3` for every member of the collection. -/
theorem fano_intersection_bundle (i : Fin 10) :
    T.intersection.surfaceIntersectionPairing T.fanoClass (T.classes i) = 3 := by
  have hsum := T.isIsotropicSequence.pairing_sum_left i
  have hnorm :
      T.intersection.surfaceIntersectionPairing ((3 : ℤ) • T.fanoClass) (T.classes i) =
        T.intersection.surfaceIntersectionPairing T.sumClass (T.classes i) := by
    simpa [fanoClass, classes, sumClass] using
      T.fano_normalization (T.bundles i).toPic
  rw [_root_.map_smul, LinearMap.smul_apply, smul_eq_mul] at hnorm
  have hsum' :
      T.intersection.surfaceIntersectionPairing T.sumClass (T.classes i) = 9 := by
    norm_num at hsum
    rw [sumClass, map_sum, LinearMap.sum_apply]
    exact hsum
  omega

/-- Symmetry gives the companion equation `Fᵢ · Δ = 3`. -/
theorem bundle_intersection_fano (i : Fin 10) :
    T.intersection.surfaceIntersectionPairing (T.classes i) T.fanoClass = 3 := by
  change T.intersection.surfaceIntersectionPairing
    (Additive.ofMul (T.bundles i).toPic) (Additive.ofMul T.fano.toPic) = 3
  rw [T.intersection.surfaceIntersectionPairing_symm]
  simpa [classes, fanoClass] using T.fano_intersection_bundle i

/-- The normalization and the ten equations `Fᵢ · Δ = 3` force `Δ² = 10`. -/
theorem fano_self_intersection :
    T.intersection.surfaceIntersectionPairing T.fanoClass T.fanoClass = 10 := by
  have hnorm :
      T.intersection.surfaceIntersectionPairing ((3 : ℤ) • T.fanoClass) T.fanoClass =
        T.intersection.surfaceIntersectionPairing T.sumClass T.fanoClass := by
    simpa [fanoClass, sumClass, classes] using T.fano_normalization T.fano.toPic
  have hsum :
      T.intersection.surfaceIntersectionPairing T.sumClass T.fanoClass = 30 := by
    calc
      T.intersection.surfaceIntersectionPairing T.sumClass T.fanoClass =
          ∑ i, T.intersection.surfaceIntersectionPairing (T.classes i) T.fanoClass := by
        rw [sumClass, map_sum, LinearMap.sum_apply]
      _ = ∑ _i : Fin 10, (3 : ℤ) :=
        Finset.sum_congr rfl fun i _ ↦ T.bundle_intersection_fano i
      _ = 30 := by norm_num
  rw [_root_.map_smul, LinearMap.smul_apply, smul_eq_mul] at hnorm
  omega

end IsotropicCollection

end AlgebraicGeometry.EnriquesSurface
