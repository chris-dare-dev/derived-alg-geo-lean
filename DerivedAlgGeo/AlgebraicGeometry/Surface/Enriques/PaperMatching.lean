/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Surface.Enriques.PaperBlocks
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Matching

/-!
# Matching Enriques exceptional blocks from their residual projections

This file specializes classification matching to the residual categories and
projection objects of the two refined Torelli papers.  A Serre-compatible
equivalence determines the reindexing: completeness supplies a target
projection up to shift, and graded orthogonality proves uniqueness.

For the singleton-block setting of Paper I this is the equality-of-count and
reordering step in Theorem 5.1.  For the block-shaped setting of Paper II it
is the first part of Theorem 3.3: blocks are matched up to reordering, and the
matching preserves the dichotomy between singleton and longer blocks.  Exact
equality of two longer block lengths is a consequence of the later extension
induction, not of the object classification alone.
-/

universe u t t'

open CategoryTheory CategoryTheory.SerreFunctor
open AlgebraicGeometry.DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.EnriquesSurface.IsotropicCollection

open Scheme.Modules

attribute [local instance] residualComponent_isTriangulated

variable {k : Type u} [Field k]
variable {Y₁ Y₂ : Scheme.{u}}
  [Y₁.Over (Spec (CommRingCat.of k))]
  [Y₂.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k Y₁] [IsSmoothProperVariety k Y₂]
variable {C₁ : SmoothProperVariety.CanonicalSheafData k Y₁ 2}
  {C₂ : SmoothProperVariety.CanonicalSheafData k Y₂ 2}
  [SmoothProperVariety.IsEnriquesSurface k Y₁ C₁]
  [SmoothProperVariety.IsEnriquesSurface k Y₂ C₂]
variable {D₁ : Cohomology.FiniteCohomology k Y₁}
  {D₂ : Cohomology.FiniteCohomology k Y₂}
  {S₁ : D₁.LinearConnectingSystem} {S₂ : D₂.LinearConnectingSystem}
variable {T₁ : IsotropicCollection (Y := Y₁) (C := C₁) D₁ S₁}
  {T₂ : IsotropicCollection (Y := Y₂) (C := C₂) D₂ S₂}
variable {exceptional₁ : T₁.ExceptionalityData}
  {exceptional₂ : T₂.ExceptionalityData}
  {semiorthogonal₁ : T₁.SemiorthogonalityData}
  {semiorthogonal₂ : T₂.SemiorthogonalityData}
variable {P₁ : T₁.PaperCategoryData exceptional₁ semiorthogonal₁}
  {P₂ : T₂.PaperCategoryData exceptional₂ semiorthogonal₂}

/-- A Serre-compatible equivalence between the two residual categories.
The compatibility remains explicit until #896--#898 derive it from an exact
linear equivalence. -/
abbrev PaperResidualSerreEquivalence
    (P₁ : T₁.PaperCategoryData exceptional₁ semiorthogonal₁)
    (P₂ : T₂.PaperCategoryData exceptional₂ semiorthogonal₂) :=
  SerreCompatibleEquivalence P₁.residualSerre.serre P₂.residualSerre.serre

namespace PaperIProjectionClassificationData

variable {B₁ : T₁.PaperBlockData exceptional₁ semiorthogonal₁ (Fin 10)}
  {B₂ : T₂.PaperBlockData exceptional₂ semiorthogonal₂ (Fin 10)}
variable {Q₁ : T₁.PaperResidualProjectionData exceptional₁ semiorthogonal₁}
  {Q₂ : T₂.PaperResidualProjectionData exceptional₂ semiorthogonal₂}
variable (A₁ : T₁.PaperIProjectionClassificationData P₁ B₁ Q₁)
  (A₂ : T₂.PaperIProjectionClassificationData P₂ B₂ Q₂)
  (F : PaperResidualSerreEquivalence P₁ P₂)

/-- The reordering of Paper I's ten singleton blocks forced by the residual
equivalence. -/
noncomputable def matchingEquiv : Fin 10 ≃ Fin 10 :=
  A₁.toSphericalClassificationData.matchingEquiv
    A₂.toSphericalClassificationData F

/-- Each Paper I projection maps to a shift of the uniquely matched target
projection. -/
theorem matchingEquiv_spec (i : Fin 10) :
    IsShiftOf (F.equiv.functor.obj (B₁.projectedObject Q₁ i))
      (B₂.projectedObject Q₂
        (PaperIProjectionClassificationData.matchingEquiv A₁ A₂ F i)) :=
  SphericalClassificationData.matchingEquiv_spec
    A₁.toSphericalClassificationData A₂.toSphericalClassificationData F i

end PaperIProjectionClassificationData

namespace PaperIIProjectionClassificationData

variable {I : Type t} {J : Type t'} [Fintype I] [Fintype J]
variable {B₁ : T₁.PaperBlockData exceptional₁ semiorthogonal₁ I}
  {B₂ : T₂.PaperBlockData exceptional₂ semiorthogonal₂ J}
variable {Q₁ : T₁.PaperResidualProjectionData exceptional₁ semiorthogonal₁}
  {Q₂ : T₂.PaperResidualProjectionData exceptional₂ semiorthogonal₂}
variable (A₁ : T₁.PaperIIProjectionClassificationData P₁ B₁ Q₁)
  (A₂ : T₂.PaperIIProjectionClassificationData P₂ B₂ Q₂)
  (F : PaperResidualSerreEquivalence P₁ P₂)

/-- The reordering of Paper II's exceptional blocks forced by the spherical
and pseudoprojective classifications. -/
noncomputable def matchingEquiv : I ≃ J :=
  A₁.toMixedClassificationData.matchingEquiv
    A₂.toMixedClassificationData F B₁.blocks.length_pos B₂.blocks.length_pos

/-- The matching preserves and reflects singleton blocks. -/
theorem matchingEquiv_length_eq_one_iff (i : I) :
    B₂.blocks.length
        (PaperIIProjectionClassificationData.matchingEquiv A₁ A₂ F i) = 1 ↔
      B₁.blocks.length i = 1 :=
  MixedClassificationData.matchingEquiv_length_eq_one_iff
    A₁.toMixedClassificationData A₂.toMixedClassificationData F
      B₁.blocks.length_pos B₂.blocks.length_pos i

/-- The matching preserves and reflects longer blocks. -/
theorem matchingEquiv_length_two_le_iff (i : I) :
    2 ≤ B₂.blocks.length
        (PaperIIProjectionClassificationData.matchingEquiv A₁ A₂ F i) ↔
      2 ≤ B₁.blocks.length i :=
  MixedClassificationData.matchingEquiv_length_two_le_iff
    A₁.toMixedClassificationData A₂.toMixedClassificationData F
      B₁.blocks.length_pos B₂.blocks.length_pos i

/-- Each Paper II projection maps to a shift of the uniquely matched target
projection. -/
theorem matchingEquiv_spec (i : I) :
    IsShiftOf (F.equiv.functor.obj (B₁.projectedObject Q₁ i))
      (B₂.projectedObject Q₂
        (PaperIIProjectionClassificationData.matchingEquiv A₁ A₂ F i)) :=
  MixedClassificationData.matchingEquiv_spec
    A₁.toMixedClassificationData A₂.toMixedClassificationData F
      B₁.blocks.length_pos B₂.blocks.length_pos i

end PaperIIProjectionClassificationData

end AlgebraicGeometry.EnriquesSurface.IsotropicCollection
