/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Topology.Category.TopCat.Opens.Limits
import DerivedAlgGeo.Topology.Category.TopCat.Opens.CoversTop
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Over
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Presentations on a basic-open cover

A quasi-coherent sheaf on an affine scheme has presentations on the members of some cover of the
open-set site. This file refines that cover to basic opens. Mathlib v4.32.1 supplies the global
quasi-coherent affine comparison; this local refinement remains a separate presentation-cover
result.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_basicOpen_presentation_cover_of_quasicoherentData`
  refines explicit quasi-coherent data to a cover by basic opens carrying presentations.
* `AlgebraicGeometry.Scheme.Modules.exists_basicOpen_presentation_cover` does the same for a
  quasi-coherent sheaf and records that the defining elements generate the unit ideal.

## Implementation notes

The cover index consists of a member `U` of the quasi-coherent presentation cover together with
a basic open contained in `U`. Every point lies in one of the original cover members, and the
basis theorem for principal opens supplies a contained `D(g)` through that point. The identity
`PrimeSpectrum.iSup_basicOpen_eq_top_iff` then turns the resulting topological cover into the
unit-ideal condition.

Restriction of presentations and quasi-coherent data to arbitrary over sites is supplied by
`Algebra.Category.ModuleCat.Sheaf.Presentation.Over`; this file begins when the open-set site
is that of `Spec R` and the cover is refined to distinguished opens. Mathlib's finite-cover
comparison proof is in `AlgebraicGeometry/Modules/Tilde.lean`; this result is not an input to
that upstream proof.

## References

* [Stacks, Tag 01IA](https://stacks.math.columbia.edu/tag/01IA), for the affine quasi-coherent
  comparison context.
* See the [affine and projective spectrum placement map](../../../../docs/architecture/placement.md)
  for the pinned source of the basic-open cover criterion.

## Tags

affine scheme, basic opens, quasi-coherent data, presentations, unit-ideal cover
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

local instance (U : TopologicalSpace.Opens (Spec R)) : HasBinaryProducts (Over U) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

/-- Explicit quasi-coherent data on `Spec R` refines to presentations on a basic-open cover. -/
theorem exists_basicOpen_presentation_cover_of_quasicoherentData
    (M : (Spec R).Modules) (q : SheafOfModules.QuasicoherentData.{u, u, u, u} M) :
    ∃ (I : Type u) (g : I → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i, Nonempty ((M.over (PrimeSpectrum.basicOpen (g i))).Presentation) := by
  let I := Σ i : q.I, {g : R // PrimeSpectrum.basicOpen g ≤ q.X i}
  let g : I → R := fun i ↦ i.2.1
  refine ⟨I, g, ?_, ?_⟩
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply TopologicalSpace.Opens.ext
    apply Set.ext
    intro x
    constructor
    · intro
      trivial
    intro hx
    obtain ⟨U, f, hf, hxU⟩ := q.coversTop ⊤ x (by simp)
    obtain ⟨i, ⟨k⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hf
    have hxXi : x ∈ q.X i := k.le hxU
    obtain ⟨V, ⟨_, ⟨a, rfl⟩, rfl⟩, hxV, hV⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxXi (q.X i).2
    rw [TopologicalSpace.Opens.coe_iSup]
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨a, hV⟩⟩, hxV⟩
  · rintro ⟨i, a, ha⟩
    let W : Over (q.X i) := Over.mk (homOfLE ha)
    exact ⟨(q.presentation i).over W⟩

/-- A quasi-coherent sheaf on `Spec R` has presentations on a basic-open cover.

The algebraic cover condition says that the defining elements generate the unit ideal; equivalently,
the corresponding basic opens have supremum `⊤`. -/
theorem exists_basicOpen_presentation_cover
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ∃ (I : Type u) (g : I → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i, Nonempty ((M.over (PrimeSpectrum.basicOpen (g i))).Presentation) := by
  obtain ⟨q⟩ :=
    SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)
  exact M.exists_basicOpen_presentation_cover_of_quasicoherentData q

end AlgebraicGeometry.Scheme.Modules
