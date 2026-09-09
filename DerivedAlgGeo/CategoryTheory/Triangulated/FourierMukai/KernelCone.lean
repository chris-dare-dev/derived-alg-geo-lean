/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ConeFunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.ExactFunctorFamily
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Basic

/-!
# Dg cone diagrams of Fourier--Mukai kernels

When the kernel category is the `H⁰` of a pretriangulated dg category, a
`DGCategory.ConePresentation` is a chosen cone diagram at the enhancement
level.  For each source object, the correspondence's kernel-evaluation functor
maps that cone triangle to a triangle in the target category.  More strongly,
a globally shift-coherent exact kernel family turns a fixed kernel cone into a
functor from source objects to distinguished transform triangles.

This module is the neutral bridge between dg cones and Fourier--Mukai
consumers.  It deliberately does not assert that a geometric correspondence
has an enhanced kernel category or that kernel evaluation is exact; those are
the derived-geometric realization obligations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v v' v'' u u' u''

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory DGCategoryStruct DGCategory Pretriangulated

variable {X : Type u} {Y : Type u'} {C : Type u''}
  [Category.{v} X] [Category.{v'} Y]
  [DGCategory.{v''} C] [IsPretriangulated C]
  [HasShift Y ℤ]

/-- The pointwise transform of the functorial dg cone family, evaluated at
one source object.  Its objects are the triangles obtained by applying kernel
evaluation to the source, target, and cone kernels; its morphisms retain the
maps induced by dg homotopy-coherent cone morphisms. -/
noncomputable def Correspondence.kernelConeTransformTriangleFunctor
    (corr : Correspondence X Y (H0 C)) (E : X)
    [(corr.kernelEvaluation E).CommShift ℤ] :
    DGCategory.ConePresentation C ⥤ Triangle Y :=
  H0.coneTriangleFunctor C ⋙ (corr.kernelEvaluation E).mapTriangle

@[simp]
theorem Correspondence.kernelConeTransformTriangleFunctor_obj₁
    (corr : Correspondence X Y (H0 C)) (E : X)
    [(corr.kernelEvaluation E).CommShift ℤ]
    (A : DGCategory.ConePresentation C) :
    ((corr.kernelConeTransformTriangleFunctor E).obj A).obj₁ =
      (corr.transform A.source).obj E := rfl

@[simp]
theorem Correspondence.kernelConeTransformTriangleFunctor_obj₂
    (corr : Correspondence X Y (H0 C)) (E : X)
    [(corr.kernelEvaluation E).CommShift ℤ]
    (A : DGCategory.ConePresentation C) :
    ((corr.kernelConeTransformTriangleFunctor E).obj A).obj₂ =
      (corr.transform A.target).obj E := rfl

@[simp]
theorem Correspondence.kernelConeTransformTriangleFunctor_obj₃
    (corr : Correspondence X Y (H0 C)) (E : X)
    [(corr.kernelEvaluation E).CommShift ℤ]
    (A : DGCategory.ConePresentation C) :
    ((corr.kernelConeTransformTriangleFunctor E).obj A).obj₃ =
      (corr.transform A.cone).obj E := rfl

/-- Exactness in the kernel variable sends every enhanced kernel cone to a
pointwise distinguished triangle of transforms. -/
theorem Correspondence.kernelConeTransformTriangleFunctor_obj_distinguished
    (corr : Correspondence X Y (H0 C)) (E : X)
    [Limits.HasZeroObject Y] [Preadditive Y]
    [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
    [(corr.kernelEvaluation E).CommShift ℤ]
    [(corr.kernelEvaluation E).IsTriangulated]
    (A : DGCategory.ConePresentation C) :
    (corr.kernelConeTransformTriangleFunctor E).obj A ∈ distTriang Y :=
  (corr.kernelEvaluation E).map_distinguished _
    (H0.coneTriangleFunctor_obj_distinguished C A)

/-- Exactness of a correspondence in the kernel variable, with shift
comparisons globally natural in the source object.

This is the Fourier--Mukai name for the generic `Functor.ExactFamily` carried
by `kernelTransform`.  In particular, its evaluated shift structures are not
independent choices: `FamilyCommShift.commShift_naturality` assembles them into
one functor-valued shift isomorphism. -/
abbrev Correspondence.KernelEvaluationExact
    (corr : Correspondence X Y (H0 C))
    [Limits.HasZeroObject Y] [Preadditive Y]
    [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y] :=
  Functor.ExactFamily corr.kernelTransform

namespace Correspondence.KernelEvaluationExact

variable {corr : Correspondence X Y (H0 C)}
  [Limits.HasZeroObject Y] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  (h : corr.KernelEvaluationExact)

/-- The pointwise transform-triangle functor obtained from a correspondence
whose kernel-variable exactness has been chosen once. -/
noncomputable def coneTriangleFunctor (E : X) :
    DGCategory.ConePresentation C ⥤ Triangle Y := by
  letI : (corr.kernelEvaluation E).CommShift ℤ := h.commShift E
  exact corr.kernelConeTransformTriangleFunctor E

@[simp]
theorem coneTriangleFunctor_obj₁ (E : X)
    (A : DGCategory.ConePresentation C) :
    ((h.coneTriangleFunctor E).obj A).obj₁ =
      (corr.transform A.source).obj E := by
  letI : (corr.kernelEvaluation E).CommShift ℤ := h.commShift E
  rfl

@[simp]
theorem coneTriangleFunctor_obj₂ (E : X)
    (A : DGCategory.ConePresentation C) :
    ((h.coneTriangleFunctor E).obj A).obj₂ =
      (corr.transform A.target).obj E := by
  letI : (corr.kernelEvaluation E).CommShift ℤ := h.commShift E
  rfl

@[simp]
theorem coneTriangleFunctor_obj₃ (E : X)
    (A : DGCategory.ConePresentation C) :
    ((h.coneTriangleFunctor E).obj A).obj₃ =
      (corr.transform A.cone).obj E := by
  letI : (corr.kernelEvaluation E).CommShift ℤ := h.commShift E
  rfl

/-- Every pointwise transform triangle supplied by kernel-variable exactness
is distinguished. -/
theorem coneTriangleFunctor_obj_distinguished (E : X)
    (A : DGCategory.ConePresentation C) :
    (h.coneTriangleFunctor E).obj A ∈ distTriang Y := by
  letI : (corr.kernelEvaluation E).CommShift ℤ := h.commShift E
  letI : (corr.kernelEvaluation E).IsTriangulated := h.triangulated E
  exact corr.kernelConeTransformTriangleFunctor_obj_distinguished E A

/-- A fixed enhanced kernel cone gives a triangle of transform functors,
natural in the source object.

This is the orientation needed by mutations and twists.  The earlier
`coneTriangleFunctor E` is recovered by evaluating this functor at `E`; it is
retained because varying the cone presentation is useful independently. -/
noncomputable def coneTriangleInSource
    (A : DGCategory.ConePresentation C) : X ⥤ Triangle Y :=
  Functor.ExactFamily.mapTriangle h (H0.coneTriangleFunctor C |>.obj A)

@[simp]
theorem coneTriangleInSource_obj_obj₁
    (A : DGCategory.ConePresentation C) (E : X) :
    ((h.coneTriangleInSource A).obj E).obj₁ =
      (corr.transform A.source).obj E :=
  rfl

@[simp]
theorem coneTriangleInSource_obj_obj₂
    (A : DGCategory.ConePresentation C) (E : X) :
    ((h.coneTriangleInSource A).obj E).obj₂ =
      (corr.transform A.target).obj E :=
  rfl

@[simp]
theorem coneTriangleInSource_obj_obj₃
    (A : DGCategory.ConePresentation C) (E : X) :
    ((h.coneTriangleInSource A).obj E).obj₃ =
      (corr.transform A.cone).obj E :=
  rfl

/-- Evaluation of the source-natural transform triangle is the previously
constructed pointwise image of the kernel cone. -/
theorem coneTriangleInSource_obj
    (A : DGCategory.ConePresentation C) (E : X) :
    (h.coneTriangleInSource A).obj E =
      (h.coneTriangleFunctor E).obj A :=
  rfl

/-- Every member of the source-natural transform triangle is distinguished. -/
theorem coneTriangleInSource_obj_distinguished
    (A : DGCategory.ConePresentation C) (E : X) :
    (h.coneTriangleInSource A).obj E ∈ distTriang Y := by
  rw [h.coneTriangleInSource_obj A E]
  exact h.coneTriangleFunctor_obj_distinguished E A

/-- The object property used as the codomain of an exact family of pointwise
kernel-cone triangles. -/
abbrev pointwiseDistinguishedTriangleProperty :
    ObjectProperty (Triangle Y) :=
  distTriang Y

/-- The pointwise kernel-cone functor with its codomain restricted to
distinguished triangles.  Consumers that need exact families can use this
functor directly instead of carrying a separate objectwise proof. -/
noncomputable def distinguishedConeTriangleFunctor (E : X) :
    DGCategory.ConePresentation C ⥤
      (pointwiseDistinguishedTriangleProperty (Y := Y)).FullSubcategory :=
  (pointwiseDistinguishedTriangleProperty (Y := Y)).lift
    (h.coneTriangleFunctor E) (h.coneTriangleFunctor_obj_distinguished E)

@[simp]
theorem distinguishedConeTriangleFunctor_obj_val (E : X)
    (A : DGCategory.ConePresentation C) :
    ((h.distinguishedConeTriangleFunctor E).obj A).obj =
      (h.coneTriangleFunctor E).obj A := rfl

/-- A fixed enhanced kernel cone as a source-indexed functor valued directly
in distinguished triangles. -/
noncomputable def distinguishedConeTriangleInSource
    (A : DGCategory.ConePresentation C) :
    X ⥤ (pointwiseDistinguishedTriangleProperty (Y := Y)).FullSubcategory :=
  (pointwiseDistinguishedTriangleProperty (Y := Y)).lift
    (h.coneTriangleInSource A) (h.coneTriangleInSource_obj_distinguished A)

@[simp]
theorem distinguishedConeTriangleInSource_obj_val
    (A : DGCategory.ConePresentation C) (E : X) :
    ((h.distinguishedConeTriangleInSource A).obj E).obj =
      (h.coneTriangleInSource A).obj E :=
  rfl

end Correspondence.KernelEvaluationExact

end CategoryTheory.Triangulated.FourierMukai
