/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.FiniteDimensional
import Mathlib.Algebra.Homology.EulerCharacteristic

/-!
# Geometric Euler characteristics of coherent sheaves

This file defines the geometric Euler characteristic

`χ(X, F) = ∑ᵢ (-1)ⁱ dimₖ Hⁱ(X, F)`

for coherent sheaves on a variety, relative to the two inputs that are not currently supplied
by Mathlib:

* the natural `k`-vector-space structure on coherent sheaf cohomology, functorial in `F`;
* finite-dimensionality and eventual vanishing.

The first input and degreewise finite-dimensionality are packaged independently in
`FiniteDimensionalCohomology`, the output interface for issue #29. `FiniteCohomology` extends
that interface only with the eventual-vanishing data tracked separately in issue #30. All
fields are hypotheses, never axioms. The projective finiteness and boundedness theorems can
later construct them without changing the definition of `χ`.

The alternating sum reuses `GradedObject.eulerChar` from Mathlib. The support theorem below
removes its possible infinite-support junk value, and `eulerCharacteristic_eq_sum` exposes the
usual finite formula. Functoriality gives invariance under isomorphism of coherent sheaves.

Additivity in short exact sequences is the next layer, implemented in
`DerivedAlgGeo.AlgebraicGeometry.Cohomology.EulerCharacteristic.Additivity`: it uses Mathlib's
additive `Ext` sequence
and requests precisely the scalar-linearity of its connecting maps.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Cohomology

variable {k : Type u} [Field k]

variable (k) in
/-- Finite-dimensional coherent cohomology together with eventual vanishing.

The inherited data is exactly the linear comparison and degreewise finiteness output of #29.
The two fields added here are the separate #30 boundedness input needed to make the Euler sum
finite. -/
structure FiniteCohomology (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsVariety k X] extends FiniteDimensionalCohomology k X where
  /-- A sheaf-dependent bound above which its cohomology vanishes. -/
  bound : Coh X → ℕ
  /-- Cohomology vanishes strictly above `bound F`. -/
  vanishesAbove : ∀ (F : Coh X) (i : ℕ), bound F < i →
    Subsingleton ((moduleH i).obj F)

namespace FiniteCohomology

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

/-- The coherent cohomology groups of `F`, regarded as a graded family of `k`-modules. -/
abbrev gradedModule (D : FiniteCohomology k X) (F : Coh X) :
    GradedObject ℕ (ModuleCat.{u + 1} k) :=
  fun i ↦ (D.moduleH i).obj F

/-- The dimension of degree-`i` coherent cohomology. -/
noncomputable abbrev dimension (D : FiniteCohomology k X) (F : Coh X) (i : ℕ) : ℕ :=
  D.toFiniteDimensionalCohomology.dimension F i

/-- The sign supplied by the cochain-complex shape is the usual `(-1)ⁱ`. -/
theorem upNat_sign (i : ℕ) : ((ComplexShape.up ℕ).χ i : ℤ) = (-1 : ℤ) ^ i := by
  change ((↑((-1 : ℤˣ) ^ i) : ℤ)) = (-1 : ℤ) ^ i
  exact Units.val_pow_eq_pow_val (-1 : ℤˣ) i

/-- The geometric Euler characteristic of a coherent sheaf. -/
noncomputable def eulerCharacteristic (D : FiniteCohomology k X) (F : Coh X) : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℕ) (D.gradedModule F)

/-- The finite-rank support of coherent cohomology lies below the supplied vanishing bound. -/
theorem finrankSupport_subset_range (D : FiniteCohomology k X) (F : Coh X) :
    GradedObject.finrankSupport (D.gradedModule F) ⊆
      (Finset.range (D.bound F + 1) : Set ℕ) := by
  intro i hi
  change D.dimension F i ≠ 0 at hi
  have hi_le : i ≤ D.bound F := by
    by_contra h
    haveI : Subsingleton ((D.moduleH i).obj F) :=
      D.vanishesAbove F i (Nat.lt_of_not_ge h)
    exact hi Module.finrank_zero_of_subsingleton
  simpa using Nat.lt_succ_of_le hi_le

/-- The Euler characteristic is the ordinary finite alternating sum through any supplied
vanishing bound. In particular, the `finsum` used by Mathlib has no junk value here. -/
theorem eulerCharacteristic_eq_sum (D : FiniteCohomology k X) (F : Coh X) :
    D.eulerCharacteristic F =
      ∑ i ∈ Finset.range (D.bound F + 1), (-1 : ℤ) ^ i * D.dimension F i := by
  simpa only [eulerCharacteristic, dimension, gradedModule, upNat_sign] using
    GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset
      (ComplexShape.up ℕ) (D.gradedModule F) (Finset.range (D.bound F + 1))
        (D.finrankSupport_subset_range F)

/-- The Euler characteristic may be summed through any bound at least as large as the
sheaf-dependent vanishing bound. -/
theorem eulerCharacteristic_eq_sum_of_bound (D : FiniteCohomology k X)
    (F : Coh X) (n : ℕ) (h : D.bound F ≤ n) :
    D.eulerCharacteristic F =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * D.dimension F i := by
  simpa only [eulerCharacteristic, dimension, gradedModule, upNat_sign] using
    GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset
      (ComplexShape.up ℕ) (D.gradedModule F) (Finset.range (n + 1)) (by
        intro i hi
        have hi' := D.finrankSupport_subset_range F hi
        have hi_lt : i < D.bound F + 1 := by
          simpa only [Finset.mem_coe, Finset.mem_range] using hi'
        simpa only [Finset.mem_coe, Finset.mem_range] using
          lt_of_lt_of_le hi_lt (Nat.add_le_add_right h 1))

/-- Isomorphic coherent sheaves have equal cohomology dimensions in every degree. -/
theorem dimension_iso (D : FiniteCohomology k X) {F G : Coh X} (e : F ≅ G) (i : ℕ) :
    D.dimension F i = D.dimension G i :=
  D.toFiniteDimensionalCohomology.dimension_iso e i

/-- The geometric Euler characteristic is invariant under isomorphism of coherent sheaves. -/
theorem eulerCharacteristic_iso (D : FiniteCohomology k X) {F G : Coh X} (e : F ≅ G) :
    D.eulerCharacteristic F = D.eulerCharacteristic G := by
  apply finsum_congr
  intro i
  change ((ComplexShape.up ℕ).χ i : ℤ) * (D.dimension F i : ℤ) =
    ((ComplexShape.up ℕ).χ i : ℤ) * (D.dimension G i : ℤ)
  rw [D.dimension_iso e i]

end FiniteCohomology

end Cohomology

end AlgebraicGeometry
