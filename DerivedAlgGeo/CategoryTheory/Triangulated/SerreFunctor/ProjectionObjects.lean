/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Projection
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Classification

/-!
# Classified residual projection objects

This file connects the generic right-adjoint projections of orthogonal
exceptional blocks to the spherical and pseudoprojective classification
interfaces.  It isolates the formal content common to Paper I, Lemma 4.8 and
Proposition 4.10, and Paper II, Lemma 2.4 and Theorem 2.7:

* the candidate attached to a block is the right projection of its first
  exceptional object;
* singleton blocks supply spherical candidates;
* longer blocks supply pseudoprojective candidates; and
* completeness and pairwise orthogonality promote these candidates to the
  existing classification packages.

The constructors below do not prove the geometric Ext calculations.  Those
remain explicit hypotheses, but the resulting classification data can no
longer hide unrelated candidate objects behind an arbitrary function.
-/

universe w v u t

namespace CategoryTheory.SerreFunctor

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Triangulated.OrthogonalExceptionalBlocks

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {ι : Type t}

attribute [local instance] OrthogonalExceptionalBlocks.residual_isTriangulated

/-- Build a spherical classification whose candidates are the actual right
projections of the first objects of exceptional blocks. -/
def SphericalClassificationData.ofResidualProjections
    (B : OrthogonalExceptionalBlocks k C ι)
    (Q : B.ResidualProjectionData)
    (D : SerreFunctorData k B.ResidualCategory) (n : ℕ)
    (candidate_spherical : ∀ i,
      IsSphericalObject D n (B.projectedObject Q i))
    (pairwise_orthogonal : ∀ {i j}, i ≠ j →
      IsGradedOrthogonal (B.projectedObject Q i) (B.projectedObject Q j))
    (complete : ∀ E : B.ResidualCategory,
      IsSphericalObject D n E ↔
        ∃ i, IsShiftOf E (B.projectedObject Q i)) :
    SphericalClassificationData D n ι where
  candidate := B.projectedObject Q
  candidate_spherical := candidate_spherical
  pairwise_orthogonal := pairwise_orthogonal
  complete := complete

@[simp]
theorem SphericalClassificationData.ofResidualProjections_candidate
    (B : OrthogonalExceptionalBlocks k C ι)
    (Q : B.ResidualProjectionData)
    (D : SerreFunctorData k B.ResidualCategory) (n : ℕ)
    (candidate_spherical) (pairwise_orthogonal) (complete) (i : ι) :
    (SphericalClassificationData.ofResidualProjections B Q D n
      candidate_spherical pairwise_orthogonal complete).candidate i =
        B.projectedObject Q i :=
  rfl

/-- Build the Paper II mixed classification with block lengths taken from the
decomposition and candidates taken from its residual right projection. -/
def MixedClassificationData.ofResidualProjections
    (B : OrthogonalExceptionalBlocks k C ι)
    (Q : B.ResidualProjectionData)
    (D : SerreFunctorData k B.ResidualCategory) (n : ℕ)
    (spherical_of_length_one : ∀ i, B.length i = 1 →
      IsSphericalObject D n (B.projectedObject Q i))
    (pseudoprojective_of_two_le : ∀ i, 2 ≤ B.length i →
      IsPseudoprojectiveObject D n (B.projectedObject Q i))
    (pairwise_orthogonal : ∀ {i j}, i ≠ j →
      IsGradedOrthogonal (B.projectedObject Q i) (B.projectedObject Q j))
    (spherical_complete : ∀ E : B.ResidualCategory,
      IsSphericalObject D n E ↔
        ∃ i, B.length i = 1 ∧ IsShiftOf E (B.projectedObject Q i))
    (pseudoprojective_complete : ∀ E : B.ResidualCategory,
      IsPseudoprojectiveObject D n E ↔
        ∃ i, 2 ≤ B.length i ∧ IsShiftOf E (B.projectedObject Q i)) :
    MixedClassificationData D n ι where
  blockLength := B.length
  candidate := B.projectedObject Q
  spherical_of_length_one := spherical_of_length_one
  pseudoprojective_of_two_le := pseudoprojective_of_two_le
  pairwise_orthogonal := pairwise_orthogonal
  spherical_complete := spherical_complete
  pseudoprojective_complete := pseudoprojective_complete

@[simp]
theorem MixedClassificationData.ofResidualProjections_blockLength
    (B : OrthogonalExceptionalBlocks k C ι)
    (Q : B.ResidualProjectionData)
    (D : SerreFunctorData k B.ResidualCategory) (n : ℕ)
    (spherical_of_length_one) (pseudoprojective_of_two_le)
    (pairwise_orthogonal) (spherical_complete) (pseudoprojective_complete)
    (i : ι) :
    (MixedClassificationData.ofResidualProjections B Q D n
      spherical_of_length_one pseudoprojective_of_two_le
      pairwise_orthogonal spherical_complete
      pseudoprojective_complete).blockLength i = B.length i :=
  rfl

@[simp]
theorem MixedClassificationData.ofResidualProjections_candidate
    (B : OrthogonalExceptionalBlocks k C ι)
    (Q : B.ResidualProjectionData)
    (D : SerreFunctorData k B.ResidualCategory) (n : ℕ)
    (spherical_of_length_one) (pseudoprojective_of_two_le)
    (pairwise_orthogonal) (spherical_complete) (pseudoprojective_complete)
    (i : ι) :
    (MixedClassificationData.ofResidualProjections B Q D n
      spherical_of_length_one pseudoprojective_of_two_le
      pairwise_orthogonal spherical_complete
      pseudoprojective_complete).candidate i = B.projectedObject Q i :=
  rfl

/-- Every residual projection candidate is spherical or pseudoprojective,
according to the positive block-length dichotomy. -/
theorem MixedClassificationData.residualProjection_candidate_dichotomy
    {B : OrthogonalExceptionalBlocks k C ι}
    {Q : B.ResidualProjectionData}
    {D : SerreFunctorData k B.ResidualCategory} {n : ℕ}
    (A : MixedClassificationData D n ι)
    (hlength : A.blockLength = B.length)
    (hcandidate : A.candidate = B.projectedObject Q) (i : ι) :
    IsSphericalObject D n (B.projectedObject Q i) ∨
      IsPseudoprojectiveObject D n (B.projectedObject Q i) := by
  rcases B.length_eq_one_or_two_le i with hi | hi
  · left
    rw [← congrFun hcandidate i]
    exact A.candidate_spherical (by simpa [hlength] using hi)
  · right
    rw [← congrFun hcandidate i]
    exact A.candidate_pseudoprojective (by simpa [hlength] using hi)

end CategoryTheory.SerreFunctor
