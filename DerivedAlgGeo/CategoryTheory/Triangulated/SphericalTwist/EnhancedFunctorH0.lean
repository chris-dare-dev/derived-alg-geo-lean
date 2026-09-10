/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionCone
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ShiftedFunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.EnhancedFunctor

/-!
# The four Anno--Logvinenko triangles, as functors on `H⁰`

`EnhancedAdjunctionCones` holds the four dg cone choices attached to a dg
functor with a left and a right dg adjoint.  Each one is a `CounitConeData` or
a `UnitConeData`, so each gives a functor into triangles of `H⁰` by the
generic construction, with every value distinguished:

| triangle | in | shape |
| --- | --- | --- |
| twist | `H⁰ B` | `S R X ⟶ X ⟶ T X ⟶ (S R X)⟦1⟧` |
| dual twist | `H⁰ B` | `C X⟦-1⟧ ⟶ X ⟶ S L X ⟶ C X` |
| cotwist | `H⁰ A` | `C' X⟦-1⟧ ⟶ X ⟶ R S X ⟶ C' X` |
| dual cotwist | `H⁰ A` | `L S X ⟶ X ⟶ T' X ⟶ (L S X)⟦1⟧` |

These are Anno--Logvinenko's four triangles read as triangles *of functors*,
which is the form their argument uses.

## The shift on two of the four is one inverse rotation

`EnhancedAdjunctionCones` stores the dual twist and the cotwist as *unshifted*
cones, because the conventional functors are their `⟦-1⟧` shifts.  Rather than
shift the cone functor and then rebuild a triangle, the triangle of the
unshifted cone is inversely rotated: `invRotate` sends `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` to
`Z⟦-1⟧ ⟶ X ⟶ Y ⟶ Z`, so it applies the shift and reorders in one step, and
`Pretriangulated.inv_rot_of_distTriang` carries distinguishedness across for
free.

The unshifted triangles are kept under their `Cone` names, since the
`TwistCotwistEquivalenceConditions` are stated against the unshifted cone
functors.

That the first vertex really is the shift of the dg cone functor, and not
merely some object isomorphic to it, is
`DGFunctor.shiftedFunctor_h0_obj`: the dg shifted functor and the `H⁰` shift
make the same choice, so the two agree on the nose.

## What is not claimed

That the twist is an autoequivalence, that the functor is spherical, or any
relation among the four triangles.  `TwistCotwistEquivalenceConditions` records
the usual equivalence pair as data and no theorem upgrades it; that implication
is Anno--Logvinenko's, and it runs through Morita quasi-functors and higher
cone coherence that this repository does not have.

Nothing here is new mathematics.  Every declaration is one line over the
generic cone-triangle layer, which is the point of having built that layer
first.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory DGCategoryStruct DGCategory Pretriangulated

namespace EnhancedAdjunctionCones

variable {A : Type u} {B : Type u'} [DGCategory.{v} A] [DGCategory.{v} B]
  {S : DGFunctor A B} {L R : DGFunctor B A} (P : EnhancedAdjunctionCones S L R)

/-! ### The two triangles in `H⁰ B` -/

section Target

variable [IsPretriangulated B]

/-- **The twist triangle.**  `S R X ⟶ X ⟶ T X ⟶ (S R X)⟦1⟧`, from the counit
of the right adjunction. -/
noncomputable def twistTriangleFunctor : H0 B ⥤ Triangle (H0 B) :=
  DGAdjunction.CounitConeData.twistTriangleFunctor P.rightAdj P.twist

theorem twistTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 B) :
    (P.twistTriangleFunctor).obj X ∈ H0.distinguishedTriangles B :=
  DGAdjunction.CounitConeData.twistTriangleFunctor_obj_mem_distinguishedTriangles
    P.rightAdj P.twist X

/-- The first map of the twist triangle is the right adjunction's counit. -/
theorem twistTriangleFunctor_obj_mor₁ (X : H0 B) :
    ((P.twistTriangleFunctor).obj X).mor₁ = P.rightAdj.h0Counit.app X :=
  DGAdjunction.CounitConeData.twistTriangleFunctor_obj_mor₁ P.rightAdj P.twist X

/-- **The unshifted dual-twist triangle.**  `X ⟶ S L X ⟶ C X ⟶ X⟦1⟧`, from the
unit of the left adjunction.  The conventional dual twist is `C⟦-1⟧`. -/
noncomputable def dualTwistConeTriangleFunctor : H0 B ⥤ Triangle (H0 B) :=
  DGAdjunction.UnitConeData.unitTriangleFunctor P.leftAdj P.dualTwistCone

theorem dualTwistConeTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 B) :
    (P.dualTwistConeTriangleFunctor).obj X ∈ H0.distinguishedTriangles B :=
  DGAdjunction.UnitConeData.unitTriangleFunctor_obj_mem_distinguishedTriangles
    P.leftAdj P.dualTwistCone X

/-- The first map of the unshifted dual-twist triangle is the left
adjunction's unit. -/
theorem dualTwistConeTriangleFunctor_obj_mor₁ (X : H0 B) :
    ((P.dualTwistConeTriangleFunctor).obj X).mor₁ = P.leftAdj.h0Unit.app X :=
  DGAdjunction.UnitConeData.unitTriangleFunctor_obj_mor₁ P.leftAdj
    P.dualTwistCone X

/-- **The dual-twist triangle.**  The inverse rotation of the unshifted one,
so its first vertex is `C X⟦-1⟧`, the dual twist:

`C X⟦-1⟧ ⟶ X ⟶ S L X ⟶ C X`.

Inverse rotation applies the shift and reorders in one step, which is why this
needs no separate shifted cone functor. -/
noncomputable def dualTwistTriangleFunctor : H0 B ⥤ Triangle (H0 B) :=
  P.dualTwistConeTriangleFunctor ⋙ invRotate (H0 B)

theorem dualTwistTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 B) :
    (P.dualTwistTriangleFunctor).obj X ∈ H0.distinguishedTriangles B :=
  inv_rot_of_distTriang _
    (P.dualTwistConeTriangleFunctor_obj_mem_distinguishedTriangles X)

/-- The first vertex of the dual-twist triangle is the dual twist: the value of
the dg cone functor, shifted by `-1`. -/
theorem dualTwistTriangleFunctor_obj_obj₁ (X : H0 B) :
    ((P.dualTwistTriangleFunctor).obj X).obj₁ =
      (P.dualTwistConeFunctor.shiftedFunctor (-1 : ℤ)).h0.obj X :=
  rfl

@[simp]
theorem dualTwistTriangleFunctor_obj_obj₂ (X : H0 B) :
    ((P.dualTwistTriangleFunctor).obj X).obj₂ = X :=
  rfl

@[simp]
theorem dualTwistTriangleFunctor_obj_obj₃ (X : H0 B) :
    ((P.dualTwistTriangleFunctor).obj X).obj₃ = (L.comp S).h0.obj X :=
  rfl

/-- The second map of the dual-twist triangle is the left adjunction's unit:
inverse rotation moves the old first map into second place. -/
theorem dualTwistTriangleFunctor_obj_mor₂ (X : H0 B) :
    ((P.dualTwistTriangleFunctor).obj X).mor₂ = P.leftAdj.h0Unit.app X :=
  P.dualTwistConeTriangleFunctor_obj_mor₁ X

end Target

/-! ### The two triangles in `H⁰ A` -/

section Source

variable [IsPretriangulated A]

/-- **The unshifted cotwist triangle.**  `X ⟶ R S X ⟶ C' X ⟶ X⟦1⟧`, from the
unit of the right adjunction.  The conventional cotwist is `C'⟦-1⟧`. -/
noncomputable def cotwistConeTriangleFunctor : H0 A ⥤ Triangle (H0 A) :=
  DGAdjunction.UnitConeData.unitTriangleFunctor P.rightAdj P.cotwistCone

theorem cotwistConeTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 A) :
    (P.cotwistConeTriangleFunctor).obj X ∈ H0.distinguishedTriangles A :=
  DGAdjunction.UnitConeData.unitTriangleFunctor_obj_mem_distinguishedTriangles
    P.rightAdj P.cotwistCone X

/-- The first map of the unshifted cotwist triangle is the right adjunction's
unit. -/
theorem cotwistConeTriangleFunctor_obj_mor₁ (X : H0 A) :
    ((P.cotwistConeTriangleFunctor).obj X).mor₁ = P.rightAdj.h0Unit.app X :=
  DGAdjunction.UnitConeData.unitTriangleFunctor_obj_mor₁ P.rightAdj
    P.cotwistCone X

/-- **The cotwist triangle.**  The inverse rotation of the unshifted one, so
its first vertex is `C' X⟦-1⟧`, the cotwist:

`C' X⟦-1⟧ ⟶ X ⟶ R S X ⟶ C' X`. -/
noncomputable def cotwistTriangleFunctor : H0 A ⥤ Triangle (H0 A) :=
  P.cotwistConeTriangleFunctor ⋙ invRotate (H0 A)

theorem cotwistTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 A) :
    (P.cotwistTriangleFunctor).obj X ∈ H0.distinguishedTriangles A :=
  inv_rot_of_distTriang _
    (P.cotwistConeTriangleFunctor_obj_mem_distinguishedTriangles X)

/-- The first vertex of the cotwist triangle is the cotwist: the value of the
dg cone functor, shifted by `-1`. -/
theorem cotwistTriangleFunctor_obj_obj₁ (X : H0 A) :
    ((P.cotwistTriangleFunctor).obj X).obj₁ =
      (P.cotwistConeFunctor.shiftedFunctor (-1 : ℤ)).h0.obj X :=
  rfl

@[simp]
theorem cotwistTriangleFunctor_obj_obj₂ (X : H0 A) :
    ((P.cotwistTriangleFunctor).obj X).obj₂ = X :=
  rfl

@[simp]
theorem cotwistTriangleFunctor_obj_obj₃ (X : H0 A) :
    ((P.cotwistTriangleFunctor).obj X).obj₃ = (S.comp R).h0.obj X :=
  rfl

/-- The second map of the cotwist triangle is the right adjunction's unit. -/
theorem cotwistTriangleFunctor_obj_mor₂ (X : H0 A) :
    ((P.cotwistTriangleFunctor).obj X).mor₂ = P.rightAdj.h0Unit.app X :=
  P.cotwistConeTriangleFunctor_obj_mor₁ X

/-- **The dual-cotwist triangle.**  `L S X ⟶ X ⟶ T' X ⟶ (L S X)⟦1⟧`, from the
counit of the left adjunction. -/
noncomputable def dualCotwistTriangleFunctor : H0 A ⥤ Triangle (H0 A) :=
  DGAdjunction.CounitConeData.twistTriangleFunctor P.leftAdj P.dualCotwist

theorem dualCotwistTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 A) :
    (P.dualCotwistTriangleFunctor).obj X ∈ H0.distinguishedTriangles A :=
  DGAdjunction.CounitConeData.twistTriangleFunctor_obj_mem_distinguishedTriangles
    P.leftAdj P.dualCotwist X

/-- The first map of the dual-cotwist triangle is the left adjunction's
counit. -/
theorem dualCotwistTriangleFunctor_obj_mor₁ (X : H0 A) :
    ((P.dualCotwistTriangleFunctor).obj X).mor₁ = P.leftAdj.h0Counit.app X :=
  DGAdjunction.CounitConeData.twistTriangleFunctor_obj_mor₁ P.leftAdj
    P.dualCotwist X

end Source

end EnhancedAdjunctionCones

end CategoryTheory.Triangulated.SphericalTwist
