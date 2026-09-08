/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Mukai.Tilting

/-!
# Geometric inputs for the Mukai tilt argument

The abstract weak-slope and Mukai-charge layers determine the imaginary part
of the tilted-heart positivity argument. Two genuinely geometric statements
remain before the exponential charge is a stability function:

* a nonzero rank-and-degree-zero torsion object has zero-dimensional Mukai
  class `(0, 0, s)` with `s > 0`;
* an object on the torsion-free boundary has a finite, nonempty decomposition
  into positive-rank boundary classes satisfying a supplied quadratic lower
  bound.

This file names those obligations without adding them to `MukaiChargeData` or
`MukaiWeakSlopeCompat`. They are object-classification results, not part of the
definition of a charge or of its compatibility with slope. A geometric K3
specialization can discharge the first from support dimension and ampleness,
and the second from stable factors plus the stable-sheaf Mukai-square bound.

The contracts are propositions rather than a bundled structure. They can be
proved independently, and consumers that need only one do not acquire the
other as an artificial field.

The most general boundary contract records the exact positive Hodge margin of
each factor. A second contract packages the common geometric situation in
which every factor satisfies one uniform lower bound `realForm ≥ -δ`. The K3
contract is only the child specialization `δ = 1`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Triangulated

universe u v

namespace CategoryTheory.Triangulated.MukaiTilt

attribute [local instance] TStructure.heartFullSubcategoryAbelian

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {t : TStructure C}

/-- **The rank-zero torsion classification needed by the tilt argument.**

Only the residual boundary case is assumed: rank and degree both vanish.
Positive-degree rank-zero torsion is already in the open upper half-plane by
`MukaiWeakSlopeCompat.im_charge_eq_degree_of_rank_zero`. -/
def HasDimensionZeroTorsionClasses
    (m : K₀ C →+ Mukai.RealExtension V) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (β ω : V) (S : WeakSlopeData t.heart.FullSubcategory) : Prop :=
  ∀ (T₀ : t.heart.FullSubcategory), ¬IsZero T₀ →
    T₀ ∈ WeakStabilityFunctionOn.hnTors S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ) →
    S.rank T₀ = 0 → S.degree T₀ = 0 →
    ∃ s : ℝ, 0 < s ∧
      (MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of T₀) = ((0 : ℝ), (0 : V), s)

/-- **The factorwise input under the exact boundary margin.**

This is the broadest geometric contract consumed by the Hodge-index assembly:
after decomposing a boundary object, every positive-rank factor must make

`2 * realForm b v + rank(v)² * b ω ω`

strictly positive. Different factors may use different bounds, and no
integrality estimate or global constant is encoded. Surface-specific APIs can
prove this directly or derive it from a more recognizable inequality such as
`realForm ≥ -δ`. -/
def HasBoundaryMukaiDecompositionWithMargin
    (m : K₀ C →+ Mukai.RealExtension V) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (β ω : V) (S : WeakSlopeData t.heart.FullSubcategory) : Prop :=
  ∀ (F₀ : t.heart.FullSubcategory), ¬IsZero F₀ →
    F₀ ∈ WeakStabilityFunctionOn.hnFree S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ) →
    S.slope F₀ = b β ω →
    ∃ (n : ℕ) (_hn : 0 < n) (G : Fin n → t.heart.FullSubcategory),
      (MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of F₀) =
          ∑ i, (MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of (G i)) ∧
        (∀ i, 0 < S.rank (G i)) ∧
        (∀ i, S.slope (G i) = b β ω) ∧
        (∀ i, 0 < 2 * Mukai.realForm b
            ((MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of (G i))) +
          ((MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of (G i))).1 ^ 2 * b ω ω)

/-- **The factorwise Mukai input at the torsion-free boundary, with an
arbitrary lower bound.**

The class equality is what additivity uses. Every factor is required to have
positive rank, the cutoff slope, and `realForm` at least `-δ`. No stability
predicate is invented here: once a geometric Jordan--Hölder API exists, its
stable factors should be used to prove this proposition.

The lower bound is parameterized because `-1` is the K3/2-CY value coming from
the stable-simple self-Ext argument, not part of boundary factorization itself.
It remains factorwise because a quadratic lower bound is not additive. -/
def HasBoundaryMukaiDecompositionWithLowerBound
    (m : K₀ C →+ Mukai.RealExtension V) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (β ω : V) (S : WeakSlopeData t.heart.FullSubcategory) (δ : ℝ) : Prop :=
  ∀ (F₀ : t.heart.FullSubcategory), ¬IsZero F₀ →
    F₀ ∈ WeakStabilityFunctionOn.hnFree S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ) →
    S.slope F₀ = b β ω →
    ∃ (n : ℕ) (_hn : 0 < n) (G : Fin n → t.heart.FullSubcategory),
      (MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of F₀) =
          ∑ i, (MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of (G i)) ∧
        (∀ i, 0 < S.rank (G i)) ∧
        (∀ i, S.slope (G i) = b β ω) ∧
        (∀ i, -δ ≤ Mukai.realForm b
          ((MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of (G i))))

/-- The historical K3-normalized boundary contract.

This is the `δ = 1` specialization of
`HasBoundaryMukaiDecompositionWithLowerBound`. It remains as a named wrapper
so existing K3 consumers keep their API while new surface realizations choose
their own geometric lower bound explicitly. -/
def HasBoundaryMukaiDecomposition
    (m : K₀ C →+ Mukai.RealExtension V) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (β ω : V) (S : WeakSlopeData t.heart.FullSubcategory) : Prop :=
  HasBoundaryMukaiDecompositionWithLowerBound m b β ω S 1

end CategoryTheory.Triangulated.MukaiTilt
