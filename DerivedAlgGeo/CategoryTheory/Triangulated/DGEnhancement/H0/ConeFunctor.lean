/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ConeCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Triangle
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Functorial dg cones in `H⁰`

The category `DGCategory.ConePresentation C` retains a closed dg arrow, a
chosen cone, and homotopy-coherent maps between such presentations.  This file
sends that category functorially to the category of triangles in `H⁰ C`.

This is stronger than choosing a triangulated cone object-by-object: identity
and composition are inherited from the explicit dg homotopies and cone maps,
and every object lands in the full subcategory of distinguished triangles.
The pretriangulated instance is needed only for the `H⁰` side, where the
chosen shift functor lives; the category of cone presentations itself needs
none.
Kernel categories and other enhanced consumers can therefore carry one
coherent cone diagram instead of separately supplying a cone and naturality
proof at every object.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v v' u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated

namespace H0

variable (C : Type u) [DGCategory.{v} C]

/-- The source vertex of a chosen dg cone presentation, functorially in
homotopy-coherent maps of presentations. -/
noncomputable def coneSourceFunctor :
    DGCategory.ConePresentation C ⥤ H0 C where
  obj A := A.source
  map m := homMk ⟨m.source, m.coneMorphism.a_closed⟩
  map_id A := rfl
  map_comp m n := by
    change homMk
        ⟨dgComp 0 0 0 (by omega) m.source n.source,
          dgComp_closed (by omega) (by omega)
            m.coneMorphism.a_closed n.coneMorphism.a_closed⟩ =
      homMk ⟨m.source, m.coneMorphism.a_closed⟩ ≫
        homMk ⟨n.source, n.coneMorphism.a_closed⟩
    rw [homMk_comp]

/-- The target vertex of a chosen dg cone presentation. -/
noncomputable def coneTargetFunctor :
    DGCategory.ConePresentation C ⥤ H0 C where
  obj A := A.target
  map m := homMk ⟨m.target, m.coneMorphism.b_closed⟩
  map_id A := rfl
  map_comp m n := by
    change homMk
        ⟨dgComp 0 0 0 (by omega) m.target n.target,
          dgComp_closed (by omega) (by omega)
            m.coneMorphism.b_closed n.coneMorphism.b_closed⟩ =
      homMk ⟨m.target, m.coneMorphism.b_closed⟩ ≫
        homMk ⟨n.target, n.coneMorphism.b_closed⟩
    rw [homMk_comp]

/-- The chosen cone vertex, with the retained closed dg cone map on
morphisms. -/
noncomputable def coneObjectFunctor :
    DGCategory.ConePresentation C ⥤ H0 C where
  obj A := A.cone
  map m := homMk m.coneMorphism.hom
  map_id A := rfl
  map_comp m n := by
    change homMk
        ⟨dgComp 0 0 0 (by omega) m.coneMorphism.hom.1
            n.coneMorphism.hom.1,
          dgComp_closed (by omega) (by omega)
            m.coneMorphism.hom.2 n.coneMorphism.hom.2⟩ =
      homMk m.coneMorphism.hom ≫ homMk n.coneMorphism.hom
    rw [homMk_comp]

@[simp]
theorem coneSourceFunctor_obj (A : DGCategory.ConePresentation C) :
    (coneSourceFunctor C).obj A = A.source := rfl

@[simp]
theorem coneSourceFunctor_map
    {A B : DGCategory.ConePresentation C} (m : A ⟶ B) :
    (coneSourceFunctor C).map m =
      homMk ⟨m.source, m.coneMorphism.a_closed⟩ := rfl

@[simp]
theorem coneTargetFunctor_obj (A : DGCategory.ConePresentation C) :
    (coneTargetFunctor C).obj A = A.target := rfl

@[simp]
theorem coneTargetFunctor_map
    {A B : DGCategory.ConePresentation C} (m : A ⟶ B) :
    (coneTargetFunctor C).map m =
      homMk ⟨m.target, m.coneMorphism.b_closed⟩ := rfl

@[simp]
theorem coneObjectFunctor_obj (A : DGCategory.ConePresentation C) :
    (coneObjectFunctor C).obj A = A.cone := rfl

@[simp]
theorem coneObjectFunctor_map
    {A B : DGCategory.ConePresentation C} (m : A ⟶ B) :
    (coneObjectFunctor C).map m = homMk m.coneMorphism.hom := rfl

variable [IsPretriangulated C]

/-- A chosen dg cone presentation determines a triangle in `H⁰`, and a
homotopy-coherent cone morphism determines a morphism of those triangles.
The construction preserves identities and composition. -/
noncomputable def coneTriangleFunctor :
    DGCategory.ConePresentation C ⥤ Triangle (H0 C) where
  obj A := coneTriangle A.arrow A.isCone
  map {A B} m := IsConeOf.Morphism.toTriangleMorphism
    A.isCone B.isCone m.coneMorphism
  map_id A := IsConeOf.Morphism.toTriangleMorphism_id A.isCone
  map_comp := by
    intro A B D m n
    change IsConeOf.Morphism.toTriangleMorphism A.isCone D.isCone
        (IsConeOf.Morphism.comp
          (hc₁ := A.isCone) (hc₂ := B.isCone) (hc₃ := D.isCone)
          m.coneMorphism n.coneMorphism) =
      IsConeOf.Morphism.toTriangleMorphism A.isCone B.isCone
          m.coneMorphism ≫
        IsConeOf.Morphism.toTriangleMorphism B.isCone D.isCone
          n.coneMorphism
    exact IsConeOf.Morphism.toTriangleMorphism_comp
      A.isCone B.isCone D.isCone m.coneMorphism n.coneMorphism

@[simp]
theorem coneTriangleFunctor_obj (A : DGCategory.ConePresentation C) :
    (coneTriangleFunctor C).obj A = coneTriangle A.arrow A.isCone := rfl

@[simp]
theorem coneTriangleFunctor_map
    {A B : DGCategory.ConePresentation C} (m : A ⟶ B) :
    (coneTriangleFunctor C).map m =
      IsConeOf.Morphism.toTriangleMorphism A.isCone B.isCone
        m.coneMorphism := rfl

/-- Every triangle in the functorial dg cone family is distinguished. -/
theorem coneTriangleFunctor_obj_distinguished
    (A : DGCategory.ConePresentation C) :
    (coneTriangleFunctor C).obj A ∈ distTriang (H0 C) :=
  coneTriangle_mem A.arrow A.isCone

/-- The object property of being a distinguished triangle in `H⁰ C`. -/
abbrev distinguishedTriangleProperty :
    ObjectProperty (Triangle (H0 C)) :=
  distTriang (H0 C)

/-- The functorial dg cone construction with its codomain restricted to the
full subcategory of distinguished triangles. -/
noncomputable def distinguishedConeTriangleFunctor :
    DGCategory.ConePresentation C ⥤
      (distinguishedTriangleProperty C).FullSubcategory :=
  (distinguishedTriangleProperty C).lift (coneTriangleFunctor C)
    (coneTriangleFunctor_obj_distinguished C)

@[simp]
theorem distinguishedConeTriangleFunctor_obj_val
    (A : DGCategory.ConePresentation C) :
    ((distinguishedConeTriangleFunctor C).obj A).obj =
      coneTriangle A.arrow A.isCone := rfl

end H0

namespace Enhancement

variable {W : Type u'} [Category.{v'} W] [HasShift W ℤ]
  (e : Enhancement.{v, u} W) [e.equiv.functor.CommShift ℤ]

/-- The functorial dg cone triangles of an enhancement, read in the enhanced
category through the comparison equivalence.  This is the form in which an
enhanced kernel category, or any other enhanced triangulated category, hands
its chosen cones to ordinary triangulated consumers. -/
noncomputable def coneTriangleFunctor :
    DGCategory.ConePresentation e.dgCat ⥤ Triangle W :=
  H0.coneTriangleFunctor e.dgCat ⋙ e.equiv.functor.mapTriangle

@[simp]
theorem coneTriangleFunctor_obj_obj₁ (A : DGCategory.ConePresentation e.dgCat) :
    (e.coneTriangleFunctor.obj A).obj₁ = e.equiv.functor.obj A.source := rfl

@[simp]
theorem coneTriangleFunctor_obj_obj₂ (A : DGCategory.ConePresentation e.dgCat) :
    (e.coneTriangleFunctor.obj A).obj₂ = e.equiv.functor.obj A.target := rfl

@[simp]
theorem coneTriangleFunctor_obj_obj₃ (A : DGCategory.ConePresentation e.dgCat) :
    (e.coneTriangleFunctor.obj A).obj₃ = e.equiv.functor.obj A.cone := rfl

/-- When the comparison equivalence is exact, every transported cone triangle
is distinguished in the enhanced category. -/
theorem coneTriangleFunctor_obj_distinguished
    [Limits.HasZeroObject W] [Preadditive W]
    [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
    [e.equiv.functor.IsTriangulated]
    (A : DGCategory.ConePresentation e.dgCat) :
    e.coneTriangleFunctor.obj A ∈ distTriang W :=
  e.equiv.functor.map_distinguished _
    (H0.coneTriangleFunctor_obj_distinguished e.dgCat A)

end Enhancement

end CategoryTheory
