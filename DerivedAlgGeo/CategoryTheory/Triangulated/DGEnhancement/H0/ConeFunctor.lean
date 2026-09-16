/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.ConeFunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Exact

/-!
# Functorial dg cones, read in a presented category

`H0.coneTriangleFunctor` is intrinsic to the dg category and is owned by
`Algebra/Homology/DGCategory/Pretriangulated/H0/ConeFunctor.lean`. This file is
the adapter: it transports those cone triangles along the comparison
equivalence of an `Enhancement`, which is where a *chosen* ordinary category
first appears.

## The two compatibilities are hypotheses, in two different strengths

Transporting a *triangle* at all needs the comparison to commute with the shift,
so `coneTriangleFunctor` below carries `[e.equiv.functor.CommShift ℤ]`.
Concluding that the transported triangle is *distinguished* needs the comparison
to be exact, so `coneTriangleFunctor_obj_distinguished` additionally carries
`[e.equiv.functor.IsTriangulated]`. Neither is proved here or anywhere else for a
general presentation; `Cdg.enhancementExact` is the one place either is
discharged.

Keeping the weaker construction under the weaker hypothesis is deliberate: a
consumer that only needs the triangle's vertices should not be made to supply
exactness it cannot prove. `Exact.coneTriangle_mem_distTriang` at the end is the
same conclusion read off the bundled refinement, for a consumer that holds one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v v' u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated

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

namespace Enhancement

section Exact

variable {W : Type u'} [Category.{v'} W] [Limits.HasZeroObject W] [Preadditive W]
  [HasShift W ℤ] [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]

/-- The same conclusion as `coneTriangleFunctor_obj_distinguished`, read off a
bundled `Enhancement.Exact` instead of two loose instance hypotheses.

This is the form a consumer that already holds the refinement wants: it supplies
one term rather than arranging for two typeclass goals to be solved, and the
`CommShift` used to transport the triangle is visibly the one the refinement
carries rather than whichever instance happened to be in scope. -/
theorem Exact.coneTriangle_mem_distTriang {e : Enhancement.{v, u} W} (h : e.Exact)
    (A : DGCategory.ConePresentation e.dgCat) :
    h.mapTriangle.obj ((H0.coneTriangleFunctor e.dgCat).obj A) ∈ distTriang W :=
  h.mapTriangle_obj_mem_distTriang _
    (H0.coneTriangleFunctor_obj_distinguished e.dgCat A)

end Exact

end Enhancement

end CategoryTheory
