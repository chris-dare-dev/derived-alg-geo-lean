/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ConeFunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.ExactFunctorFamily
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Basic

/-!
# Dg cone diagrams of Fourier--Mukai kernels

When the kernel category `W` of a correspondence carries a dg enhancement
`e : Enhancement W`, a `DGCategory.ConePresentation e.dgCat` is a chosen cone
diagram at the enhancement level, and `e.coneTriangleFunctor` reads it as a
triangle of kernels.  For each source object, the correspondence's
kernel-evaluation functor maps that triangle to a triangle in the target
category.  More strongly, a globally shift-coherent exact kernel family turns
a fixed kernel cone into a functor from source objects to distinguished
transform triangles.

The kernel category is *enhanced*, not identified with an `H⁰` on the nose:
a geometric kernel category such as `Dᵇ(Coh(X × Y))` is only equivalent to
the `H⁰` of its enhancement, and the comparison equivalence is exactly the
datum `Enhancement` carries.  The shift and exactness compatibility of that
comparison are instance hypotheses here; supplying them for a concrete
enhancement is part of the geometric realization, as is exactness of kernel
evaluation itself.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v v' v'' vE u u' u'' uE

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory DGCategoryStruct DGCategory Pretriangulated

variable {X : Type u} {Y : Type u'} {W : Type u''}
  [Category.{v} X] [Category.{v'} Y] [Category.{v''} W]
  [HasShift Y ℤ] [HasShift W ℤ]
  (e : Enhancement.{vE, uE} W) [e.equiv.functor.CommShift ℤ]

/-- The pointwise transform of the functorial dg cone family of an enhanced
kernel category, evaluated at one source object.  Its objects are the
triangles obtained by applying kernel evaluation to the source, target, and
cone kernels; its morphisms retain the maps induced by dg homotopy-coherent
cone morphisms. -/
noncomputable def Correspondence.kernelConeTransformTriangleFunctor
    (corr : Correspondence X Y W) (E : X)
    [(corr.kernelEvaluation E).CommShift ℤ] :
    DGCategory.ConePresentation e.dgCat ⥤ Triangle Y :=
  e.coneTriangleFunctor ⋙ (corr.kernelEvaluation E).mapTriangle

@[simp]
theorem Correspondence.kernelConeTransformTriangleFunctor_obj₁
    (corr : Correspondence X Y W) (E : X)
    [(corr.kernelEvaluation E).CommShift ℤ]
    (A : DGCategory.ConePresentation e.dgCat) :
    ((corr.kernelConeTransformTriangleFunctor e E).obj A).obj₁ =
      (corr.transform (e.equiv.functor.obj A.source)).obj E := rfl

@[simp]
theorem Correspondence.kernelConeTransformTriangleFunctor_obj₂
    (corr : Correspondence X Y W) (E : X)
    [(corr.kernelEvaluation E).CommShift ℤ]
    (A : DGCategory.ConePresentation e.dgCat) :
    ((corr.kernelConeTransformTriangleFunctor e E).obj A).obj₂ =
      (corr.transform (e.equiv.functor.obj A.target)).obj E := rfl

@[simp]
theorem Correspondence.kernelConeTransformTriangleFunctor_obj₃
    (corr : Correspondence X Y W) (E : X)
    [(corr.kernelEvaluation E).CommShift ℤ]
    (A : DGCategory.ConePresentation e.dgCat) :
    ((corr.kernelConeTransformTriangleFunctor e E).obj A).obj₃ =
      (corr.transform (e.equiv.functor.obj A.cone)).obj E := rfl

variable [Limits.HasZeroObject Y] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  [Limits.HasZeroObject W] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]

/-- Exactness in the kernel variable sends every enhanced kernel cone to a
pointwise distinguished triangle of transforms. -/
theorem Correspondence.kernelConeTransformTriangleFunctor_obj_distinguished
    (corr : Correspondence X Y W) (E : X)
    [e.equiv.functor.IsTriangulated]
    [(corr.kernelEvaluation E).CommShift ℤ]
    [(corr.kernelEvaluation E).IsTriangulated]
    (A : DGCategory.ConePresentation e.dgCat) :
    (corr.kernelConeTransformTriangleFunctor e E).obj A ∈ distTriang Y :=
  (corr.kernelEvaluation E).map_distinguished _
    (e.coneTriangleFunctor_obj_distinguished A)

/-- Exactness of a correspondence in the kernel variable, with shift
comparisons globally natural in the source object.

This is the Fourier--Mukai name for the generic `Functor.ExactFamily` carried
by `kernelTransform`.  In particular, its evaluated shift structures are not
independent choices: `FamilyCommShift.commShift_naturality` assembles them into
one functor-valued shift isomorphism. -/
abbrev Correspondence.KernelEvaluationExact (corr : Correspondence X Y W) :=
  Functor.ExactFamily corr.kernelTransform

namespace Correspondence.KernelEvaluationExact

variable {corr : Correspondence X Y W} (h : corr.KernelEvaluationExact)

/-- The pointwise transform-triangle functor obtained from a correspondence
whose kernel-variable exactness has been chosen once. -/
noncomputable def coneTriangleFunctor (E : X) :
    DGCategory.ConePresentation e.dgCat ⥤ Triangle Y := by
  letI : (corr.kernelEvaluation E).CommShift ℤ := h.commShift E
  exact corr.kernelConeTransformTriangleFunctor e E

@[simp]
theorem coneTriangleFunctor_obj₁ (E : X)
    (A : DGCategory.ConePresentation e.dgCat) :
    ((h.coneTriangleFunctor e E).obj A).obj₁ =
      (corr.transform (e.equiv.functor.obj A.source)).obj E := by
  letI : (corr.kernelEvaluation E).CommShift ℤ := h.commShift E
  rfl

@[simp]
theorem coneTriangleFunctor_obj₂ (E : X)
    (A : DGCategory.ConePresentation e.dgCat) :
    ((h.coneTriangleFunctor e E).obj A).obj₂ =
      (corr.transform (e.equiv.functor.obj A.target)).obj E := by
  letI : (corr.kernelEvaluation E).CommShift ℤ := h.commShift E
  rfl

@[simp]
theorem coneTriangleFunctor_obj₃ (E : X)
    (A : DGCategory.ConePresentation e.dgCat) :
    ((h.coneTriangleFunctor e E).obj A).obj₃ =
      (corr.transform (e.equiv.functor.obj A.cone)).obj E := by
  letI : (corr.kernelEvaluation E).CommShift ℤ := h.commShift E
  rfl

/-- Every pointwise transform triangle supplied by kernel-variable exactness
is distinguished. -/
theorem coneTriangleFunctor_obj_distinguished [e.equiv.functor.IsTriangulated] (E : X)
    (A : DGCategory.ConePresentation e.dgCat) :
    (h.coneTriangleFunctor e E).obj A ∈ distTriang Y := by
  letI : (corr.kernelEvaluation E).CommShift ℤ := h.commShift E
  letI : (corr.kernelEvaluation E).IsTriangulated := h.triangulated E
  exact corr.kernelConeTransformTriangleFunctor_obj_distinguished e E A

/-- A fixed enhanced kernel cone gives a triangle of transform functors,
natural in the source object.

This is the orientation needed by mutations and twists.  The earlier
`coneTriangleFunctor E` is recovered by evaluating this functor at `E`; it is
retained because varying the cone presentation is useful independently. -/
noncomputable def coneTriangleInSource
    (A : DGCategory.ConePresentation e.dgCat) : X ⥤ Triangle Y :=
  Functor.ExactFamily.mapTriangle h (e.coneTriangleFunctor.obj A)

@[simp]
theorem coneTriangleInSource_obj_obj₁
    (A : DGCategory.ConePresentation e.dgCat) (E : X) :
    ((h.coneTriangleInSource e A).obj E).obj₁ =
      (corr.transform (e.equiv.functor.obj A.source)).obj E :=
  rfl

@[simp]
theorem coneTriangleInSource_obj_obj₂
    (A : DGCategory.ConePresentation e.dgCat) (E : X) :
    ((h.coneTriangleInSource e A).obj E).obj₂ =
      (corr.transform (e.equiv.functor.obj A.target)).obj E :=
  rfl

@[simp]
theorem coneTriangleInSource_obj_obj₃
    (A : DGCategory.ConePresentation e.dgCat) (E : X) :
    ((h.coneTriangleInSource e A).obj E).obj₃ =
      (corr.transform (e.equiv.functor.obj A.cone)).obj E :=
  rfl

/-- Evaluation of the source-natural transform triangle is the previously
constructed pointwise image of the kernel cone. -/
theorem coneTriangleInSource_obj
    (A : DGCategory.ConePresentation e.dgCat) (E : X) :
    (h.coneTriangleInSource e A).obj E =
      (h.coneTriangleFunctor e E).obj A :=
  rfl

/-- Every member of the source-natural transform triangle is distinguished. -/
theorem coneTriangleInSource_obj_distinguished [e.equiv.functor.IsTriangulated]
    (A : DGCategory.ConePresentation e.dgCat) (E : X) :
    (h.coneTriangleInSource e A).obj E ∈ distTriang Y := by
  rw [h.coneTriangleInSource_obj e A E]
  exact h.coneTriangleFunctor_obj_distinguished e E A

/-- The object property used as the codomain of an exact family of pointwise
kernel-cone triangles. -/
abbrev pointwiseDistinguishedTriangleProperty :
    ObjectProperty (Triangle Y) :=
  distTriang Y

/-- The pointwise kernel-cone functor with its codomain restricted to
distinguished triangles.  Consumers that need exact families can use this
functor directly instead of carrying a separate objectwise proof. -/
noncomputable def distinguishedConeTriangleFunctor [e.equiv.functor.IsTriangulated] (E : X) :
    DGCategory.ConePresentation e.dgCat ⥤
      (pointwiseDistinguishedTriangleProperty (Y := Y)).FullSubcategory :=
  (pointwiseDistinguishedTriangleProperty (Y := Y)).lift
    (h.coneTriangleFunctor e E) (h.coneTriangleFunctor_obj_distinguished e E)

@[simp]
theorem distinguishedConeTriangleFunctor_obj_val [e.equiv.functor.IsTriangulated] (E : X)
    (A : DGCategory.ConePresentation e.dgCat) :
    ((h.distinguishedConeTriangleFunctor e E).obj A).obj =
      (h.coneTriangleFunctor e E).obj A := rfl

/-- A fixed enhanced kernel cone as a source-indexed functor valued directly
in distinguished triangles. -/
noncomputable def distinguishedConeTriangleInSource [e.equiv.functor.IsTriangulated]
    (A : DGCategory.ConePresentation e.dgCat) :
    X ⥤ (pointwiseDistinguishedTriangleProperty (Y := Y)).FullSubcategory :=
  (pointwiseDistinguishedTriangleProperty (Y := Y)).lift
    (h.coneTriangleInSource e A) (h.coneTriangleInSource_obj_distinguished e A)

@[simp]
theorem distinguishedConeTriangleInSource_obj_val [e.equiv.functor.IsTriangulated]
    (A : DGCategory.ConePresentation e.dgCat) (E : X) :
    ((h.distinguishedConeTriangleInSource e A).obj E).obj =
      (h.coneTriangleInSource e A).obj E :=
  rfl

end Correspondence.KernelEvaluationExact

end CategoryTheory.Triangulated.FourierMukai
