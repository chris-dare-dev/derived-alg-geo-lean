/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PeriodDomain
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.Bounds
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Finitely many spherical walls pass through a point of the period domain

`PeriodDomain.neg_of_mem_orthogonal` makes `Q` negative definite on `Wᗮ` for
every positive plane `W` of a space of signature `(2, n - 2)`.  The reusable
continuity and coercivity results now live in `Continuous.lean` and
`Bounds.lean`; this file spends them on spherical classes and lattice walls.

## Main results

* `PeriodDomain.finite_sphericalOrthogonal_inter` — **for a lattice `Λ`, only
  finitely many spherical classes of `Λ` are orthogonal to a given positive
  plane**, i.e. `finite_walls_through`: finitely many spherical walls pass
  through a point of the period domain.

## What is *not* proved here, and why it is not an oversight

The region-wise statement — finitely many walls meet a *family* of positive
planes — does not follow. The coercivity constant of `-Q` on `Wᗮ` depends on
`W` and degrades to `0` as the plane approaches the boundary of the
positive-plane locus, so a bounded family of planes does not by itself supply a
uniform constant. This is one of the two gaps in Bridgeland's own §11 argument.
The other chart already answers it the honest way: `Walls/Spherical/Finiteness.lean`
makes `coercivity` an explicit field of `BoundedRegion` rather than deriving it.
A region-wise route (A) statement must do the same, and is deliberately left to
its own change.

Everything below is about an arbitrary real quadratic space and its lattices;
`Λ` is the `ℤ`-span of an `ℝ`-basis and is **not** asserted to be `N(X)`, in the
discipline of `LinearAlgebra/Lattice/Mukai/Basic.lean`.
-/

open Bornology QuadraticMap

namespace PeriodDomain

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
variable {Q : QuadraticForm ℝ M} {W : Submodule ℝ M}

/-- The spherical classes orthogonal to `W`. By `mem_wall_iff_mem_orthogonal`
these are exactly the classes whose wall passes through `W`. -/
def sphericalOrthogonal (Q : QuadraticForm ℝ M) (W : Submodule ℝ M) : Set M :=
  {δ | IsSphericalClass Q δ ∧ δ ∈ orthogonal Q W}

/-- **The spherical classes orthogonal to a positive plane form a bounded set.**

`Q` is negative definite on `Wᗮ`, so `-Q` is a positive definite form there and
`-Q δ = 1` confines `δ` to a level set, which is bounded. -/
theorem isBounded_sphericalOrthogonal (hsig : HasSignatureTwo Q)
    (hW : IsPositivePlane Q W) : IsBounded (sphericalOrthogonal Q W) := by
  obtain ⟨c, hc, hle⟩ := (negDef_orthogonal hsig hW).exists_pos_mul_norm_sq_le
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Real.sqrt (1 / c), ?_⟩
  rintro δ ⟨hsph, hmem⟩
  have h := hle ⟨δ, hmem⟩
  have hval : ((-Q).restrict (orthogonal Q W)) ⟨δ, hmem⟩ = 1 := by
    rw [restrict_apply]
    simp [isSphericalClass_iff_apply.mp hsph]
  rw [hval] at h
  have hnorm : ‖(⟨δ, hmem⟩ : orthogonal Q W)‖ = ‖δ‖ := rfl
  rw [hnorm] at h
  have hsq : ‖δ‖ ^ 2 ≤ 1 / c := by
    rw [le_div_iff₀ hc]
    linarith
  exact (Real.le_sqrt (norm_nonneg δ) (by positivity)).mpr hsq

/-- **Only finitely many spherical classes of a lattice are orthogonal to a
given positive plane.**

Bounded by `isBounded_sphericalOrthogonal`, and a lattice meets a bounded set
finitely. `Λ` is the `ℤ`-span of an `ℝ`-basis; nothing identifies it with a
geometric lattice. -/
theorem finite_sphericalOrthogonal_inter (hsig : HasSignatureTwo Q)
    (hW : IsPositivePlane Q W) {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ M) :
    (sphericalOrthogonal Q W ∩ (Submodule.span ℤ (Set.range b) : Set M)).Finite :=
  ZSpan.setFinite_inter b (isBounded_sphericalOrthogonal hsig hW)

/-- **Finitely many spherical walls pass through a point of the period domain.**

The same statement as `finite_sphericalOrthogonal_inter`, said in walls: this is
what a local-finiteness argument for route (A) starts from, and the pointwise
case is unconditional where the region-wise case is not. -/
theorem finite_walls_through (hsig : HasSignatureTwo Q) (hW : IsPositivePlane Q W)
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ M) :
    {δ : M | IsSphericalClass Q δ ∧ W ∈ wall Q δ ∧
      δ ∈ (Submodule.span ℤ (Set.range b) : Set M)}.Finite := by
  refine Set.Finite.subset (finite_sphericalOrthogonal_inter hsig hW b) ?_
  rintro δ ⟨hsph, hwall, hlat⟩
  exact ⟨⟨hsph, (mem_wall_iff_mem_orthogonal hW).mp hwall⟩, hlat⟩

end PeriodDomain
