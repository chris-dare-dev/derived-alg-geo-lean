/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionCone
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
| dual twist, unshifted | `H⁰ B` | `X ⟶ S L X ⟶ C X ⟶ X⟦1⟧` |
| cotwist, unshifted | `H⁰ A` | `X ⟶ R S X ⟶ C' X ⟶ X⟦1⟧` |
| dual cotwist | `H⁰ A` | `L S X ⟶ X ⟶ T' X ⟶ (L S X)⟦1⟧` |

These are Anno--Logvinenko's four triangles read as triangles *of functors*,
which is the form their argument uses.

## Two of the four are unshifted, and that is not a slip

The conventional dual twist and cotwist are the `⟦-1⟧` shifts of the two cone
functors named above, and `EnhancedFunctor.lean` says so where those fields are
declared.  The triangles here are of the unshifted cones.  Applying the shift
needs the degree coherence of `DGFunctor.shiftedFunctorAdd`, and relating the
shifted triangle to this one needs a rotation argument; neither is done here,
and the names carry `Cone` where the cone rather than the conventional functor
is what appears.

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
