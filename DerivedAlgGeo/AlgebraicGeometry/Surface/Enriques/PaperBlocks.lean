/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Surface.Enriques.PaperObjects
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.ProjectionObjects

/-!
# Exceptional blocks and residual projection objects in the Enriques papers

This file formalizes the common paper-content layer of
arXiv:1912.04332v2, Setup 4.5 and Lemmas 4.7--4.8, and
arXiv:2104.13610v2, Proposition 1.4, Setup 2.5, Lemma 2.4, and Theorem 2.7.

An `PaperBlockData` partitions the ten selected exceptional line bundles into
positive-length, mutually orthogonal exceptional blocks.  Its residual is
identified with the already constructed neutral residual component.  A
`PaperResidualProjectionData` then chooses the right adjoint to the residual
inclusion, and `projectedObject` is exactly the paper's
`S_i := ζ_K^!(L_{i1})`.

The spherical, pseudoprojective, orthogonality, and completeness statements
remain supplied theorem data: their proofs use mutation triangles and Ext
computations not yet constructed in the repository.  The new classification
constructors ensure, however, that these theorems concern the actual residual
projections of the actual block objects, rather than arbitrary candidates.

The chains of `(-2)`-curves appearing in Paper II, Proposition 1.4 and the
mutation/Ext consequences they feed are recorded in the downstream
`PaperExtension` module.
-/

universe u t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.ObjectProperty
open CategoryTheory.SerreFunctor
open AlgebraicGeometry.DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.EnriquesSurface.IsotropicCollection

open Scheme.Modules

variable {k : Type u} [Field k]
variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k Y]
variable {C : SmoothProperVariety.CanonicalSheafData k Y 2}
  [SmoothProperVariety.IsEnriquesSurface k Y C]
variable {D : Cohomology.FiniteCohomology k Y} {S : D.LinearConnectingSystem}
variable (T : IsotropicCollection (Y := Y) (C := C) D S)

attribute [local instance] residualComponent_isTriangulated

/-- A block-shaped presentation of the ten selected exceptional line bundles.

`bundleIndex` and `bundleIso` say that the dependent family of block members
is precisely the original family of ten bundles, up to reindexing and
isomorphism.  `residual_eq` records that taking the right orthogonal after
grouping into triangulated block spans gives the same neutral residual
property already constructed in `Enriques.Residual`. -/
structure PaperBlockData (exceptional : T.ExceptionalityData)
    (semiorthogonal : T.SemiorthogonalityData) (ι : Type t) [Fintype ι] where
  /-- The mutually orthogonal exceptional blocks. -/
  blocks : OrthogonalExceptionalBlocks k (DerivedCat Y) ι
  /-- The block positions enumerate exactly ten objects. -/
  bundleIndex : (Σ i, Fin (blocks.length i)) ≃ Fin 10
  /-- Each block member is the corresponding selected line bundle. -/
  bundleIso : ∀ x : Σ i, Fin (blocks.length i),
    (blocks.collection x.1).obj x.2 ≅
      (T.bundles (bundleIndex x)).boundedDerivedObject
  /-- Grouping the exceptional objects into blocks does not change their
  residual right orthogonal. -/
  residual_eq : blocks.residual =
    T.residualComponent exceptional semiorthogonal

namespace PaperBlockData

variable {T}
variable {exceptional : T.ExceptionalityData}
  {semiorthogonal : T.SemiorthogonalityData}
variable {ι : Type t} [Fintype ι]
variable (B : T.PaperBlockData exceptional semiorthogonal ι)

/-- The block lengths sum to ten, derived from the supplied enumeration rather
than stored as a second numerical field. -/
theorem totalLength_eq_ten : B.blocks.totalLength = 10 := by
  have h := Fintype.card_congr B.bundleIndex
  simpa [OrthogonalExceptionalBlocks.totalLength] using h

include B in
/-- The entries of the unordered block-decomposition type sum to ten. -/
theorem decompositionType_sum_eq_ten : B.blocks.decompositionType.sum = 10 := by
  rw [B.blocks.decompositionType_sum, B.totalLength_eq_ten]

include B in
/-- The number of blocks is at most ten. -/
theorem card_le_ten : Fintype.card ι ≤ 10 := by
  rw [← totalLength_eq_ten B]
  exact B.blocks.card_le_totalLength

/-- The original bundle index corresponding to the first member of block
`i`. -/
noncomputable def firstBundleIndex (i : ι) : Fin 10 :=
  B.bundleIndex ⟨i, B.blocks.firstIndex i⟩

/-- The first object of a block is one of the original ten bounded derived
line bundles. -/
noncomputable def firstObjectIso (i : ι) :
    B.blocks.firstObject i ≅
      (T.bundles (B.firstBundleIndex i)).boundedDerivedObject :=
  B.bundleIso ⟨i, B.blocks.firstIndex i⟩

/-- Every block is either a singleton block or a longer block. -/
theorem singleton_or_longer (i : ι) :
    B.blocks.length i = 1 ∨ 2 ≤ B.blocks.length i :=
  B.blocks.length_eq_one_or_two_le i

end PaperBlockData

/-- A chosen right-adjoint projection from the ambient derived category onto
the already constructed residual category. -/
abbrev PaperResidualProjectionData
    (exceptional : T.ExceptionalityData)
    (semiorthogonal : T.SemiorthogonalityData) :=
  RightProjectionData (T.residualComponent exceptional semiorthogonal)

namespace PaperBlockData

variable {T}
variable {exceptional : T.ExceptionalityData}
  {semiorthogonal : T.SemiorthogonalityData}
variable {ι : Type t} [Fintype ι]
variable (B : T.PaperBlockData exceptional semiorthogonal ι)

/-- The paper's residual projection object
`S_i := ζ_K^!(L_{i1})`. -/
noncomputable abbrev projectedObject
    (Q : T.PaperResidualProjectionData exceptional semiorthogonal) (i : ι) :
    T.ResidualCategory exceptional semiorthogonal :=
  Q.project (B.blocks.firstObject i)

/-- Paper I, Remark 4.9(i), in its formal adjunction form: maps from a
residual object to `S_i` are ambient maps to the first object of block `i`. -/
noncomputable def projectedObjectHomEquiv
    (Q : T.PaperResidualProjectionData exceptional semiorthogonal)
    (R : T.ResidualCategory exceptional semiorthogonal) (i : ι) :
    (R ⟶ B.projectedObject Q i) ≃
      ((T.residualComponent exceptional semiorthogonal).ι.obj R ⟶
        B.blocks.firstObject i) :=
  Q.homEquivFromProject R (B.blocks.firstObject i)

/-- The identity of `S_i` corresponds to its projection counit
`S_i → L_{i1}`. -/
theorem projectedObjectHomEquiv_id
    (Q : T.PaperResidualProjectionData exceptional semiorthogonal) (i : ι) :
    B.projectedObjectHomEquiv Q (B.projectedObject Q i) i
        (𝟙 (B.projectedObject Q i)) =
      Q.counitApp (B.blocks.firstObject i) :=
  Q.homEquivFromProject_id (B.blocks.firstObject i)

end PaperBlockData

/-- Paper I's singleton-block projection statements and classification.
This combines Lemma 4.8 and Proposition 4.10 while fixing the candidate
family to the residual projections above. -/
structure PaperIProjectionClassificationData
    {exceptional : T.ExceptionalityData}
    {semiorthogonal : T.SemiorthogonalityData}
    (P : T.PaperCategoryData exceptional semiorthogonal)
    (B : T.PaperBlockData exceptional semiorthogonal (Fin 10))
    (Q : T.PaperResidualProjectionData exceptional semiorthogonal) : Prop where
  /-- Paper I has ten singleton blocks. -/
  singleton : ∀ i, B.blocks.length i = 1
  /-- Each residual projection is `3`-spherical. -/
  spherical : ∀ i,
    IsSphericalObject P.residualSerre.serre 3 (B.projectedObject Q i)
  /-- Projections from distinct blocks are graded-orthogonal. -/
  pairwise_orthogonal : ∀ {i j}, i ≠ j →
    IsGradedOrthogonal (B.projectedObject Q i) (B.projectedObject Q j)
  /-- Every `3`-spherical residual object is a shift of one projection. -/
  complete : ∀ E : T.ResidualCategory exceptional semiorthogonal,
    IsSphericalObject P.residualSerre.serre 3 E ↔
      ∃ i, IsShiftOf E (B.projectedObject Q i)

namespace PaperIProjectionClassificationData

variable {T}
variable {exceptional : T.ExceptionalityData}
  {semiorthogonal : T.SemiorthogonalityData}
variable {P : T.PaperCategoryData exceptional semiorthogonal}
variable {B : T.PaperBlockData exceptional semiorthogonal (Fin 10)}
variable {Q : T.PaperResidualProjectionData exceptional semiorthogonal}
variable (A : T.PaperIProjectionClassificationData P B Q)

/-- Forget the block/projection realization and recover the previously landed
Paper I classification interface. -/
noncomputable def toSphericalClassificationData :
    T.PaperISphericalClassificationData P where
  candidate := B.projectedObject Q
  candidate_spherical := A.spherical
  pairwise_orthogonal := A.pairwise_orthogonal
  complete := A.complete

@[simp]
theorem toSphericalClassificationData_candidate (i : Fin 10) :
    A.toSphericalClassificationData.candidate i = B.projectedObject Q i :=
  rfl

include A in
/-- Exact Paper I classification for the actual residual projection objects. -/
theorem spherical_iff
    (E : T.ResidualCategory exceptional semiorthogonal) :
    IsSphericalObject P.residualSerre.serre 3 E ↔
      ∃ i : Fin 10, IsShiftOf E (B.projectedObject Q i) :=
  A.complete E

include A in
/-- Every Paper I residual projection object is nonzero. -/
theorem projectedObject_not_isZero (i : Fin 10) :
    ¬ IsZero (B.projectedObject Q i) :=
  (A.spherical i).not_isZero

include A in
/-- Distinct Paper I projection objects are not isomorphic up to shift. -/
theorem projectedObject_not_shift {i j : Fin 10} (hij : i ≠ j) :
    ¬ IsShiftOf (B.projectedObject Q i) (B.projectedObject Q j) :=
  SphericalClassificationData.candidate_not_isShiftOf
    A.toSphericalClassificationData hij

end PaperIProjectionClassificationData

/-- Paper II's block-sensitive projection statements and classification.
The first three fields are Lemma 2.4; the final two are Theorem 2.7. -/
structure PaperIIProjectionClassificationData
    {exceptional : T.ExceptionalityData}
    {semiorthogonal : T.SemiorthogonalityData}
    (P : T.PaperCategoryData exceptional semiorthogonal)
    {ι : Type t} [Fintype ι]
    (B : T.PaperBlockData exceptional semiorthogonal ι)
    (Q : T.PaperResidualProjectionData exceptional semiorthogonal) : Prop where
  /-- Singleton blocks produce `3`-spherical residual projections. -/
  spherical_of_singleton : ∀ i, B.blocks.length i = 1 →
    IsSphericalObject P.residualSerre.serre 3 (B.projectedObject Q i)
  /-- Longer blocks produce `3`-pseudoprojective residual projections. -/
  pseudoprojective_of_longer : ∀ i, 2 ≤ B.blocks.length i →
    IsPseudoprojectiveObject P.residualSerre.serre 3 (B.projectedObject Q i)
  /-- Projections from distinct blocks are graded-orthogonal. -/
  pairwise_orthogonal : ∀ {i j}, i ≠ j →
    IsGradedOrthogonal (B.projectedObject Q i) (B.projectedObject Q j)
  /-- Classification of all `3`-spherical residual objects. -/
  spherical_complete :
    ∀ E : T.ResidualCategory exceptional semiorthogonal,
      IsSphericalObject P.residualSerre.serre 3 E ↔
        ∃ i, B.blocks.length i = 1 ∧
          IsShiftOf E (B.projectedObject Q i)
  /-- Classification of all `3`-pseudoprojective residual objects. -/
  pseudoprojective_complete :
    ∀ E : T.ResidualCategory exceptional semiorthogonal,
      IsPseudoprojectiveObject P.residualSerre.serre 3 E ↔
        ∃ i, 2 ≤ B.blocks.length i ∧
          IsShiftOf E (B.projectedObject Q i)

namespace PaperIIProjectionClassificationData

variable {T}
variable {exceptional : T.ExceptionalityData}
  {semiorthogonal : T.SemiorthogonalityData}
variable {P : T.PaperCategoryData exceptional semiorthogonal}
variable {ι : Type t} [Fintype ι]
variable {B : T.PaperBlockData exceptional semiorthogonal ι}
variable {Q : T.PaperResidualProjectionData exceptional semiorthogonal}
variable (A : T.PaperIIProjectionClassificationData P B Q)

/-- Forget the block/projection realization and recover the previously landed
Paper II mixed classification interface. -/
noncomputable def toMixedClassificationData :
    T.PaperIIObjectClassificationData P ι where
  blockLength := B.blocks.length
  candidate := B.projectedObject Q
  spherical_of_length_one :=
    PaperIIProjectionClassificationData.spherical_of_singleton A
  pseudoprojective_of_two_le :=
    PaperIIProjectionClassificationData.pseudoprojective_of_longer A
  pairwise_orthogonal := A.pairwise_orthogonal
  spherical_complete := A.spherical_complete
  pseudoprojective_complete := A.pseudoprojective_complete

@[simp]
theorem toMixedClassificationData_blockLength (i : ι) :
    A.toMixedClassificationData.blockLength i = B.blocks.length i :=
  rfl

@[simp]
theorem toMixedClassificationData_candidate (i : ι) :
    A.toMixedClassificationData.candidate i = B.projectedObject Q i :=
  rfl

include A in
/-- Exact spherical half of Paper II's classification for the actual residual
projection objects of singleton blocks. -/
theorem spherical_iff
    (E : T.ResidualCategory exceptional semiorthogonal) :
    IsSphericalObject P.residualSerre.serre 3 E ↔
      ∃ i, B.blocks.length i = 1 ∧
        IsShiftOf E (B.projectedObject Q i) :=
  A.spherical_complete E

include A in
/-- Exact pseudoprojective half of Paper II's classification for the actual
residual projection objects of longer blocks. -/
theorem pseudoprojective_iff
    (E : T.ResidualCategory exceptional semiorthogonal) :
    IsPseudoprojectiveObject P.residualSerre.serre 3 E ↔
      ∃ i, 2 ≤ B.blocks.length i ∧
        IsShiftOf E (B.projectedObject Q i) :=
  A.pseudoprojective_complete E

include A in
/-- Every Paper II projection object is either `3`-spherical or
`3`-pseudoprojective. -/
theorem projectedObject_dichotomy (i : ι) :
    IsSphericalObject P.residualSerre.serre 3 (B.projectedObject Q i) ∨
      IsPseudoprojectiveObject P.residualSerre.serre 3
        (B.projectedObject Q i) := by
  rcases B.singleton_or_longer i with hi | hi
  · exact Or.inl
      (PaperIIProjectionClassificationData.spherical_of_singleton A i hi)
  · exact Or.inr
      (PaperIIProjectionClassificationData.pseudoprojective_of_longer A i hi)

include A in
/-- Every Paper II residual projection object is nonzero. -/
theorem projectedObject_not_isZero (i : ι) :
    ¬ IsZero (B.projectedObject Q i) := by
  rcases A.projectedObject_dichotomy i with hi | hi
  · exact hi.not_isZero
  · exact hi.not_isZero

include A in
/-- A longer-block residual projection cannot also be spherical. -/
theorem longer_projectedObject_not_spherical {i : ι}
    (hi : 2 ≤ B.blocks.length i) :
    ¬ IsSphericalObject P.residualSerre.serre 3
      (B.projectedObject Q i) :=
  IsPseudoprojectiveObject.not_isSphericalObject
    (PaperIIProjectionClassificationData.pseudoprojective_of_longer A i hi)
    (by omega)

include A in
/-- Distinct singleton-block projection objects are not isomorphic up to
shift. -/
theorem singleton_projectedObject_not_shift {i j : ι}
    (hi : B.blocks.length i = 1) (hij : i ≠ j) :
    ¬ IsShiftOf (B.projectedObject Q i) (B.projectedObject Q j) :=
  MixedClassificationData.spherical_candidate_not_isShiftOf
    A.toMixedClassificationData hi hij

include A in
/-- Distinct longer-block projection objects are not isomorphic up to shift. -/
theorem longer_projectedObject_not_shift {i j : ι}
    (hi : 2 ≤ B.blocks.length i) (hij : i ≠ j) :
    ¬ IsShiftOf (B.projectedObject Q i) (B.projectedObject Q j) :=
  MixedClassificationData.pseudoprojective_candidate_not_isShiftOf
    A.toMixedClassificationData hi hij

end PaperIIProjectionClassificationData

end AlgebraicGeometry.EnriquesSurface.IsotropicCollection
