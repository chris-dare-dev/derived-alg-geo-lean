/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Admissible
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Blocks
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Right-adjoint projections onto admissible components

For a full subcategory cut out by an object property `P`, a right projection
is a chosen right adjoint to the inclusion `P.ι`.  The distinction between
existence and chosen data is intentional: `P.IsRightAdmissible` is a
proposition, while the Enriques papers form concrete objects such as
`ζ_K^!(L)` and therefore need an actual projection functor.

This file packages only the adjunction.  It does not call a cone functor or
construct mutations: functorial cones are unavailable in a bare triangulated
category.  The adjunction nevertheless gives the universal Hom equivalence
used in Paper I, Remark 4.9, and in Paper II's definition of the residual
projection objects.
-/

open CategoryTheory

universe v u t

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- A chosen right-adjoint projection onto the full subcategory defined by
`P`. -/
structure RightProjectionData where
  /-- The right projection functor. -/
  projection : C ⥤ P.FullSubcategory
  /-- The inclusion is left adjoint to the projection. -/
  adjunction : P.ι ⊣ projection

namespace RightProjectionData

variable {P} (Q : RightProjectionData P)

/-- The projected object, as an object of the full subcategory. -/
abbrev project (X : C) : P.FullSubcategory :=
  Q.projection.obj X

/-- The underlying ambient object of a projection. -/
abbrev projectObj (X : C) : C :=
  P.ι.obj (Q.project X)

/-- The counit map from the projected ambient object to its source. -/
abbrev counitApp (X : C) : Q.projectObj X ⟶ X :=
  Q.adjunction.counit.app X

/-- The universal property of the right projection. -/
def homEquiv (R : P.FullSubcategory) (X : C) :
    (P.ι.obj R ⟶ X) ≃ (R ⟶ Q.project X) :=
  Q.adjunction.homEquiv R X

/-- The universal property in the direction used by residual-category
consumers: maps from a residual object to the projected object are exactly
ambient maps to the original object. -/
def homEquivFromProject (R : P.FullSubcategory) (X : C) :
    (R ⟶ Q.project X) ≃ (P.ι.obj R ⟶ X) :=
  (Q.adjunction.homEquiv R X).symm

/-- Under the universal Hom equivalence, the identity of a projected object
corresponds to the counit map. -/
theorem homEquivFromProject_id (X : C) :
    Q.homEquivFromProject (Q.project X) X (𝟙 (Q.project X)) =
      Q.counitApp X :=
  Q.adjunction.homEquiv_symm_id X

include Q in
/-- Chosen projection data witnesses proposition-valued right
admissibility once triangulated closure of the component is known. -/
theorem isRightAdmissible
    [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (hP : P.IsTriangulated) : P.IsRightAdmissible :=
  ⟨hP, Q.projection, ⟨Q.adjunction⟩⟩

section Zero

variable [Preadditive C]

/-- The projection of `X` is zero exactly when every ambient map from a
`P`-object to `X` vanishes. -/
theorem project_isZero_iff (X : C) :
    Limits.IsZero (Q.project X) ↔
      ∀ (R : P.FullSubcategory) (f : P.ι.obj R ⟶ X), f = 0 := by
  letI : Q.projection.Additive := Q.adjunction.right_adjoint_additive
  constructor
  · intro h R f
    apply (Q.homEquiv R X).injective
    exact h.eq_of_tgt _ _
  · intro h
    rw [Limits.IsZero.iff_id_eq_zero]
    apply (Q.homEquivFromProject (Q.project X) X).injective
    rw [Q.homEquivFromProject_id]
    exact (h (Q.project X) (Q.counitApp X)).trans (by
      change 0 = (Q.adjunction.homEquiv (Q.project X) X).symm 0
      exact (Q.adjunction.homAddEquiv_symm_zero (Q.project X) X).symm)

end Zero

end RightProjectionData

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Triangulated.OrthogonalExceptionalBlocks

open ObjectProperty

variable {k : Type*} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {ι : Type t}

/-- A chosen right projection onto the residual category of an exceptional
block decomposition. -/
abbrev ResidualProjectionData (B : OrthogonalExceptionalBlocks k C ι) :=
  RightProjectionData B.residual

/-- The residual projection of the first exceptional object in block `i`.
This is the common categorical shape of the objects `S_i` in both Enriques
papers. -/
abbrev projectedObject (B : OrthogonalExceptionalBlocks k C ι)
    (Q : B.ResidualProjectionData) (i : ι) : B.ResidualCategory :=
  Q.project (B.firstObject i)

/-- Universal property of a residual projection object. -/
def projectedObjectHomEquiv (B : OrthogonalExceptionalBlocks k C ι)
    (Q : B.ResidualProjectionData) (R : B.ResidualCategory) (i : ι) :
    (R ⟶ B.projectedObject Q i) ≃
      (B.residual.ι.obj R ⟶ B.firstObject i) :=
  Q.homEquivFromProject R (B.firstObject i)

/-- The identity of a residual projection object corresponds to its counit
map into the first exceptional object of the block. -/
theorem projectedObjectHomEquiv_id
    (B : OrthogonalExceptionalBlocks k C ι)
    (Q : B.ResidualProjectionData) (i : ι) :
    B.projectedObjectHomEquiv Q (B.projectedObject Q i) i
        (𝟙 (B.projectedObject Q i)) =
      Q.counitApp (B.firstObject i) :=
  Q.homEquivFromProject_id (B.firstObject i)

end CategoryTheory.Triangulated.OrthogonalExceptionalBlocks
