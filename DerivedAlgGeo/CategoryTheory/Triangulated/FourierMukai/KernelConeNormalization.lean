/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.KernelCone

/-!
# Normalizing transformed kernel cones

A fixed enhanced kernel cone gives a source-natural triangle whose first two
vertices are transforms of the enhancement's chosen endpoint lifts.  Concrete
applications usually present those transforms by more meaningful functors and
identify the first map with a named natural transformation.

`Correspondence.KernelConeNormalizationData` packages exactly that endpoint
comparison square.  Together with exactness in the kernel variable, it
transports the raw cone triangle to a source-natural triangle with literal
first map and literal first two vertices.  The construction reuses Mathlib's
`Triangle.functorMk` and `Triangle.functorIsoMk`.

The result is only a family of pointwise distinguished triangles.  It does not
give a distinguished triangle in a functor category, make the third functor
exact, or compare different enhanced arrows or cone choices.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe vX vY vW vE uX uY uW uE

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory DGCategoryStruct DGCategory Pretriangulated

variable {X : Type uX} {Y : Type uY} {W : Type uW}
  [Category.{vX} X] [Category.{vY} Y] [Category.{vW} W]

/-- Endpoint data identifying the transformed arrow of an enhanced kernel cone
with a named natural transformation between literal functors.

The isomorphisms point from the raw endpoint transforms to the literal
functors, so `square` is exactly the first square needed to compare the raw
cone triangle with its normalized form. -/
structure Correspondence.KernelConeNormalizationData
    (corr : Correspondence X Y W) (e : Enhancement.{vE, uE} W)
    (A : DGCategory.ConePresentation e.dgCat)
    (F G : X ⥤ Y) (α : F ⟶ G) where
  /-- Comparison from the raw source transform to the literal source functor. -/
  sourceIso : corr.transform (e.equiv.functor.obj A.source) ≅ F
  /-- Comparison from the raw target transform to the literal target functor. -/
  targetIso : corr.transform (e.equiv.functor.obj A.target) ≅ G
  /-- The transformed enhanced arrow is the named natural transformation after
  the endpoint comparisons. -/
  square :
    corr.transformMap
        (e.equiv.functor.map (H0.homMk (C := e.dgCat) A.arrow)) ≫
        targetIso.hom =
      sourceIso.hom ≫ α

namespace Correspondence.KernelConeNormalizationData

variable {corr : Correspondence X Y W} {e : Enhancement.{vE, uE} W}
  {A : DGCategory.ConePresentation e.dgCat} {F G : X ⥤ Y} {α : F ⟶ G}
  (N : corr.KernelConeNormalizationData e A F G α)

/-- The transform of the selected cone, with no application-specific name. -/
abbrev coneTransform : X ⥤ Y :=
  let _ := N
  corr.transform (e.equiv.functor.obj A.cone)

section Exact

variable [Limits.HasZeroObject Y] [HasShift Y ℤ] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ] (h : corr.KernelEvaluationExact)

/-- The unnormalized source-natural triangle obtained by transforming the
enhanced kernel cone. -/
noncomputable def rawTriangle : X ⥤ Triangle Y :=
  let _ := N
  h.coneTriangleInSource e A

@[simp]
theorem rawTriangle_obj₁ (E : X) :
    ((N.rawTriangle h).obj E).obj₁ =
      (corr.transform (e.equiv.functor.obj A.source)).obj E :=
  rfl

@[simp]
theorem rawTriangle_obj₂ (E : X) :
    ((N.rawTriangle h).obj E).obj₂ =
      (corr.transform (e.equiv.functor.obj A.target)).obj E :=
  rfl

@[simp]
theorem rawTriangle_obj₃ (E : X) :
    ((N.rawTriangle h).obj E).obj₃ = N.coneTransform.obj E :=
  rfl

/-- The first map of the raw transform triangle. -/
theorem rawTriangle_mor₁ :
    Functor.whiskerLeft (N.rawTriangle h) Triangle.π₁Toπ₂ =
      corr.transformMap
        (e.equiv.functor.map (H0.homMk (C := e.dgCat) A.arrow)) :=
  rfl

/-- The source comparison typed against the first projection of the raw
triangle functor. -/
noncomputable def rawTriangleObj₁Iso :
    N.rawTriangle h ⋙ Triangle.π₁ ≅ F := by
  change corr.transform (e.equiv.functor.obj A.source) ≅ F
  exact N.sourceIso

/-- The target comparison typed against the second projection of the raw
triangle functor. -/
noncomputable def rawTriangleObj₂Iso :
    N.rawTriangle h ⋙ Triangle.π₂ ≅ G := by
  change corr.transform (e.equiv.functor.obj A.target) ≅ G
  exact N.targetIso

/-- The first comparison square, stated against the raw triangle functor. -/
theorem rawTriangle_square :
    Functor.whiskerLeft (N.rawTriangle h) Triangle.π₁Toπ₂ ≫
        (N.rawTriangleObj₂Iso h).hom =
      (N.rawTriangleObj₁Iso h).hom ≫ α := by
  exact N.square

/-- The transported second map from the literal target functor to the cone
transform. -/
noncomputable def normalizedSecond : G ⟶ N.coneTransform :=
  (N.rawTriangleObj₂Iso h).inv ≫
    Functor.whiskerLeft (N.rawTriangle h) Triangle.π₂Toπ₃

/-- The transported connecting map from the cone transform to the shifted
literal source functor. -/
noncomputable def normalizedThird :
    N.coneTransform ⟶ F ⋙ shiftFunctor Y (1 : ℤ) :=
  Functor.whiskerLeft (N.rawTriangle h) Triangle.π₃Toπ₁ ≫
    Functor.whiskerRight (N.rawTriangleObj₁Iso h).hom
      (shiftFunctor Y (1 : ℤ))

/-- The normalized source-natural triangle with literal first map and literal
first two vertices. -/
noncomputable def normalizedTriangle : X ⥤ Triangle Y :=
  Triangle.functorMk α (N.normalizedSecond h) (N.normalizedThird h)

@[simp]
theorem normalizedTriangle_obj₁ (E : X) :
    ((N.normalizedTriangle h).obj E).obj₁ = F.obj E :=
  rfl

@[simp]
theorem normalizedTriangle_obj₂ (E : X) :
    ((N.normalizedTriangle h).obj E).obj₂ = G.obj E :=
  rfl

@[simp]
theorem normalizedTriangle_obj₃ (E : X) :
    ((N.normalizedTriangle h).obj E).obj₃ = N.coneTransform.obj E :=
  rfl

@[simp]
theorem normalizedTriangle_mor₁ (E : X) :
    ((N.normalizedTriangle h).obj E).mor₁ = α.app E :=
  rfl

@[simp]
theorem normalizedTriangle_mor₂ (E : X) :
    ((N.normalizedTriangle h).obj E).mor₂ =
      (N.normalizedSecond h).app E :=
  rfl

@[simp]
theorem normalizedTriangle_mor₃ (E : X) :
    ((N.normalizedTriangle h).obj E).mor₃ =
      (N.normalizedThird h).app E :=
  rfl

/-- The raw transform triangle and its endpoint-normalized form are naturally
isomorphic. -/
noncomputable def rawTriangleIsoNormalized :
    N.rawTriangle h ≅ N.normalizedTriangle h :=
  Triangle.functorIsoMk _ _ (N.rawTriangleObj₁Iso h)
    (N.rawTriangleObj₂Iso h) (Iso.refl _)
    (N.rawTriangle_square h)
    (by
      ext E
      change ((N.rawTriangle h).obj E).mor₂ ≫ 𝟙 _ =
        (N.rawTriangleObj₂Iso h).hom.app E ≫
          ((N.rawTriangleObj₂Iso h).inv.app E ≫
            ((N.rawTriangle h).obj E).mor₂)
      rw [Category.comp_id]
      exact (Iso.hom_inv_id_assoc
        ((N.rawTriangleObj₂Iso h).app E)
        ((N.rawTriangle h).obj E).mor₂).symm)
    (by
      ext E
      change ((N.rawTriangle h).obj E).mor₃ ≫
          (shiftFunctor Y (1 : ℤ)).map
            ((N.rawTriangleObj₁Iso h).hom.app E) =
        𝟙 _ ≫ (((N.rawTriangle h).obj E).mor₃ ≫
          (shiftFunctor Y (1 : ℤ)).map
            ((N.rawTriangleObj₁Iso h).hom.app E))
      simp)

@[simp]
theorem rawTriangleIsoNormalized_hom_app_hom₁ (E : X) :
    ((N.rawTriangleIsoNormalized h).hom.app E).hom₁ =
      (N.rawTriangleObj₁Iso h).hom.app E :=
  rfl

@[simp]
theorem rawTriangleIsoNormalized_hom_app_hom₂ (E : X) :
    ((N.rawTriangleIsoNormalized h).hom.app E).hom₂ =
      (N.rawTriangleObj₂Iso h).hom.app E :=
  rfl

@[simp]
theorem rawTriangleIsoNormalized_hom_app_hom₃ (E : X) :
    ((N.rawTriangleIsoNormalized h).hom.app E).hom₃ = 𝟙 _ :=
  rfl

/-- Every value of the normalized triangle is distinguished. -/
theorem normalizedTriangle_obj_distinguished
    [e.equiv.functor.IsTriangulated] (E : X) :
    (N.normalizedTriangle h).obj E ∈ distTriang Y :=
  (distinguished_iff_of_iso ((N.rawTriangleIsoNormalized h).app E)).mp
    (h.coneTriangleInSource_obj_distinguished e A E)

/-- The normalized family with codomain restricted to distinguished
triangles. -/
noncomputable def distinguishedNormalizedTriangle
    [e.equiv.functor.IsTriangulated] :
    X ⥤ (Correspondence.KernelEvaluationExact.pointwiseDistinguishedTriangleProperty
      (Y := Y)).FullSubcategory :=
  (Correspondence.KernelEvaluationExact.pointwiseDistinguishedTriangleProperty
    (Y := Y)).lift (N.normalizedTriangle h)
      (N.normalizedTriangle_obj_distinguished h)

@[simp]
theorem distinguishedNormalizedTriangle_obj_val
    [e.equiv.functor.IsTriangulated] (E : X) :
    ((N.distinguishedNormalizedTriangle h).obj E).obj =
      (N.normalizedTriangle h).obj E :=
  rfl

end Exact

end Correspondence.KernelConeNormalizationData

end CategoryTheory.Triangulated.FourierMukai
