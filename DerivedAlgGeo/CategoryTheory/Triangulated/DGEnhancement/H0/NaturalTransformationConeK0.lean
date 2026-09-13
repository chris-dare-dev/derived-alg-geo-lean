/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ConeExactness
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Functor
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.NaturalTransformationCone
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial

/-!
# Grothendieck-group action of a functorial dg cone

A closed degree-zero dg natural transformation `α : F ⟶ G` with chosen
objectwise cones gives a functorial distinguished triangle

`H⁰ F X ⟶ H⁰ G X ⟶ H⁰(Cone α) X ⟶ H⁰ F X⟦1⟧`.

Consequently its cone functor has class `[G X] - [F X]`.  When both endpoints
preserve chosen dg cones, all three functors are exact on `H⁰`, and the same
formula holds as an equality of homomorphisms on `K₀`.

This generic leaf is the owner of the subtraction formula.  Adjunction cones,
object twists, and any later kernel-cone construction should specialize it
rather than repeat the triangle calculation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated Triangulated

namespace DGFunctor.HomogeneousNatTrans.ConeData

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]
  [IsPretriangulated D]
  {F G : DGFunctor C D} {α : HomogeneousNatTrans F G 0}
  (K : ConeData α)

/-- The functorial cone triangle gives
`[Cone(α) X] = [G X] - [F X]` in `K₀(H⁰ D)`. -/
theorem functorK₀Of (hα : IsClosed α) (X : H0 C) :
    K₀.of (H0 D) (K.functor.h0.obj X) =
      K₀.of (H0 D) (G.h0.obj X) - K₀.of (H0 D) (F.h0.obj X) := by
  have h := K₀.of_triangle (H0 D) ((K.triangleFunctor hα).obj X)
    (K.triangleFunctor_obj_mem_distinguishedTriangles hα X)
  change K₀.of (H0 D) (G.h0.obj X) =
    K₀.of (H0 D) (F.h0.obj X) +
      K₀.of (H0 D) (K.functor.h0.obj X) at h
  rw [h]
  abel

variable [IsPretriangulated C]

set_option backward.isDefEq.respectTransparency false in
/-- The functorial cone acts on `K₀` by target endpoint minus source endpoint.
The endpoint cone arguments are retained for source compatibility and are
redundant. -/
theorem functorK₀Map
    (hα : IsClosed α)
    (hFc : DGFunctor.PreservesChosenCones F)
    (hGc : DGFunctor.PreservesChosenCones G) :
    letI : K.functor.h0.CommShift ℤ :=
      DGFunctor.commShift _ K.preservesShifts
    letI : K.functor.h0.IsTriangulated :=
      DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
        K.preservesShifts (K.preservesChosenCones hFc hGc)
    letI : F.h0.CommShift ℤ :=
      DGFunctor.commShift _ (DGFunctor.preservesShifts _)
    letI : F.h0.IsTriangulated :=
      DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
        (DGFunctor.preservesShifts _) hFc
    letI : G.h0.CommShift ℤ :=
      DGFunctor.commShift _ (DGFunctor.preservesShifts _)
    letI : G.h0.IsTriangulated :=
      DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
        (DGFunctor.preservesShifts _) hGc
    K₀.map K.functor.h0 = K₀.map G.h0 - K₀.map F.h0 := by
  letI : K.functor.h0.CommShift ℤ :=
    DGFunctor.commShift _ K.preservesShifts
  letI : K.functor.h0.IsTriangulated :=
    DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
      K.preservesShifts (K.preservesChosenCones hFc hGc)
  letI : F.h0.CommShift ℤ :=
    DGFunctor.commShift _ (DGFunctor.preservesShifts _)
  letI : F.h0.IsTriangulated :=
    DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
      (DGFunctor.preservesShifts _) hFc
  letI : G.h0.CommShift ℤ :=
    DGFunctor.commShift _ (DGFunctor.preservesShifts _)
  letI : G.h0.IsTriangulated :=
    DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
      (DGFunctor.preservesShifts _) hGc
  apply K₀.hom_ext
  intro X
  change K₀.of (H0 D) (K.functor.h0.obj X) =
    K₀.of (H0 D) (G.h0.obj X) - K₀.of (H0 D) (F.h0.obj X)
  exact K.functorK₀Of hα X

end DGFunctor.HomogeneousNatTrans.ConeData

end CategoryTheory
