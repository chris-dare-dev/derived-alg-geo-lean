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
  into positive-rank boundary factors satisfying a supplied predicate.

This file names those obligations without adding them to `MukaiChargeData` or
`MukaiWeakSlopeCompat`. They are object-classification results, not part of the
definition of a charge or of its compatibility with slope. A geometric K3
specialization can discharge the first from support dimension and ampleness,
and the second from stable factors plus the stable-sheaf Mukai-square bound.

The contracts are propositions rather than a bundled structure. They can be
proved independently, and consumers that need only one do not acquire the
other as an artificial field.

The boundary contract is parameterized by a predicate on the factors:
`HasBoundaryMukaiDecompositionWith P` asks only for a nonempty decomposition
into positive-rank factors at the cutoff, each satisfying `P`. Which predicate
a surface can supply, and why it forces `Re Z > 0`, is decided by the consumer;
`Mukai/Tilting.lean` proves it for the exact Hodge margin and for a uniform
lower bound `realForm ≥ -δ`. The margin and `δ` contracts are abbreviations of
the parent, and the K3 contract is only the child specialization `δ = 1`.
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

/-- **Boundary decomposition into factors satisfying a predicate.**

This is the parent contract of the boundary case. A nonzero object of the
torsion-free class sitting exactly on the cutoff must admit a nonempty finite
family of factors whose Mukai classes sum to its class, each of positive rank,
each on the cutoff, and each satisfying `P`. Positive rank and the cutoff slope
are what put every factor on `Im Z = 0`; they are not surface-specific. The
predicate `P` is the only surface-specific input, and the contract does not say
how `P` forces `Re Z > 0`: a consumer proves that separately and hands it to
`MukaiWeakSlopeCompat.mem_semiClosedUpperHalfPlane_of_shift_hnFree_of_pred`.

For coherent sheaves the factors are the Jordan--Hölder factors of a
`μ`-semistable sheaf (an object of the torsion-free class whose slope equals
the cutoff is forced to be semistable), and `P` records whatever bound the
surface provides for a stable sheaf. Different surfaces differ only in `P`. -/
def HasBoundaryMukaiDecompositionWith
    (m : K₀ C →+ Mukai.RealExtension V) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (β ω : V) (S : WeakSlopeData t.heart.FullSubcategory)
    (P : t.heart.FullSubcategory → Prop) : Prop :=
  ∀ (F₀ : t.heart.FullSubcategory), ¬IsZero F₀ →
    F₀ ∈ WeakStabilityFunctionOn.hnFree S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ) →
    S.slope F₀ = b β ω →
    ∃ (n : ℕ) (_hn : 0 < n) (G : Fin n → t.heart.FullSubcategory),
      (MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of F₀) =
          ∑ i, (MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of (G i)) ∧
        (∀ i, 0 < S.rank (G i)) ∧
        (∀ i, S.slope (G i) = b β ω) ∧
        (∀ i, P (G i))

/-- **The factorwise input under the exact boundary margin.**

The predicate is the exact quantity the Hodge-index estimate places below
`2 * r * Re Z`:

`0 < 2 * realForm b v + rank(v)² * b ω ω`.

Different factors may use different bounds, and no integrality estimate or
global constant is encoded. Surface-specific APIs can prove this directly or
derive it from a more recognizable inequality such as `realForm ≥ -δ`. -/
def HasBoundaryMukaiDecompositionWithMargin
    (m : K₀ C →+ Mukai.RealExtension V) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (β ω : V) (S : WeakSlopeData t.heart.FullSubcategory) : Prop :=
  HasBoundaryMukaiDecompositionWith m b β ω S fun G ↦
    0 < 2 * Mukai.realForm b ((MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of G)) +
      ((MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of G)).1 ^ 2 * b ω ω

/-- **The factorwise Mukai input at the torsion-free boundary, with an
arbitrary lower bound.**

Every factor is required to have `realForm` at least `-δ`. No stability
predicate is invented here: once a geometric Jordan--Hölder API exists, its
stable factors should be used to prove this proposition.

The lower bound is parameterized because `-1` is the K3/2-CY value coming from
the stable-simple self-Ext argument, not part of boundary factorization itself.
It remains factorwise because a quadratic lower bound is not additive. -/
def HasBoundaryMukaiDecompositionWithLowerBound
    (m : K₀ C →+ Mukai.RealExtension V) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (β ω : V) (S : WeakSlopeData t.heart.FullSubcategory) (δ : ℝ) : Prop :=
  HasBoundaryMukaiDecompositionWith m b β ω S fun G ↦
    -δ ≤ Mukai.realForm b ((MukaiChargeData.ofAmbient t m).mukai (K₀Ab.of G))

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
