/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.EnhancedFunctorH0

/-!
# Grothendieck-group actions of enhanced adjunction cones

The four distinguished adjunction triangles determine the `K₀` class of
each conventional twist or cotwist value.  Under chosen-cone preservation for
the two endpoints, exactness upgrades those generator formulas to equalities
of homomorphisms on `K₀`.

These formulas stop at the adjunction composites.  Identifying an
object-twist evaluation composite with
`chiHom k C E X • K₀.of C E` is the separate copower/Euler-characteristic
seam needed to recover the numerical reflection `twistK₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory DGCategoryStruct DGCategory Pretriangulated

namespace EnhancedAdjunctionCones

variable {A : Type u} {B : Type u'} [DGCategory.{v} A] [DGCategory.{v} B]
  {S : DGFunctor A B} {L R : DGFunctor B A} (P : EnhancedAdjunctionCones S L R)

section Target

variable [IsPretriangulated B]

/-- The twist triangle gives `[T X] = [X] - [S R X]` in `K₀(H⁰ B)`. -/
theorem twistFunctorK₀Of (X : H0 B) :
    K₀.of (H0 B) (P.twistFunctor.h0.obj X) =
      K₀.of (H0 B) X - K₀.of (H0 B) ((R.comp S).h0.obj X) := by
  have h := K₀.of_triangle (H0 B) ((P.twistTriangleFunctor).obj X)
    (P.twistTriangleFunctor_obj_mem_distinguishedTriangles X)
  change K₀.of (H0 B) X =
    K₀.of (H0 B) ((R.comp S).h0.obj X) +
      K₀.of (H0 B) (P.twistFunctor.h0.obj X) at h
  rw [h]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- When `S` and `R` preserve chosen cones, the twist acts on `K₀` by the
identity minus the adjunction composite. -/
theorem twistFunctorK₀Map
    (hSc : DGFunctor.PreservesChosenCones S)
    (hRc : DGFunctor.PreservesChosenCones R) :
    letI : P.twistFunctor.h0.CommShift ℤ := P.twistH0CommShift
    letI : P.twistFunctor.h0.IsTriangulated :=
      P.twistH0IsTriangulated hSc hRc
    letI : (R.comp S).h0.CommShift ℤ :=
      DGFunctor.commShift _ (DGFunctor.preservesShifts _)
    letI : (R.comp S).h0.IsTriangulated :=
      DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
        (DGFunctor.preservesShifts _)
        (DGFunctor.PreservesChosenCones.comp hRc hSc)
    K₀.map P.twistFunctor.h0 =
      AddMonoidHom.id (K₀ (H0 B)) - K₀.map (R.comp S).h0 := by
  letI : P.twistFunctor.h0.CommShift ℤ := P.twistH0CommShift
  letI : P.twistFunctor.h0.IsTriangulated :=
    P.twistH0IsTriangulated hSc hRc
  letI : (R.comp S).h0.CommShift ℤ :=
    DGFunctor.commShift _ (DGFunctor.preservesShifts _)
  letI : (R.comp S).h0.IsTriangulated :=
    DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
      (DGFunctor.preservesShifts _)
      (DGFunctor.PreservesChosenCones.comp hRc hSc)
  apply K₀.hom_ext
  intro X
  change K₀.of (H0 B) (P.twistFunctor.h0.obj X) =
    K₀.of (H0 B) X - K₀.of (H0 B) ((R.comp S).h0.obj X)
  exact P.twistFunctorK₀Of X

/-- The dual-twist triangle gives `[T' X] = [X] - [S L X]` in
`K₀(H⁰ B)`. -/
theorem dualTwistFunctorK₀Of (X : H0 B) :
    K₀.of (H0 B) (P.dualTwistFunctor.h0.obj X) =
      K₀.of (H0 B) X - K₀.of (H0 B) ((L.comp S).h0.obj X) := by
  have h := K₀.of_triangle (H0 B) ((P.dualTwistTriangleFunctor).obj X)
    (P.dualTwistTriangleFunctor_obj_mem_distinguishedTriangles X)
  change K₀.of (H0 B) X =
    K₀.of (H0 B) (P.dualTwistFunctor.h0.obj X) +
      K₀.of (H0 B) ((L.comp S).h0.obj X) at h
  rw [h]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- When `L` and `S` preserve chosen cones, the dual twist acts on `K₀` by
the identity minus the left-adjunction composite. -/
theorem dualTwistFunctorK₀Map
    (hLc : DGFunctor.PreservesChosenCones L)
    (hSc : DGFunctor.PreservesChosenCones S) :
    letI : P.dualTwistFunctor.h0.CommShift ℤ := P.dualTwistH0CommShift
    letI : P.dualTwistFunctor.h0.IsTriangulated :=
      P.dualTwistH0IsTriangulated hLc hSc
    letI : (L.comp S).h0.CommShift ℤ :=
      DGFunctor.commShift _ (DGFunctor.preservesShifts _)
    letI : (L.comp S).h0.IsTriangulated :=
      DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
        (DGFunctor.preservesShifts _)
        (DGFunctor.PreservesChosenCones.comp hLc hSc)
    K₀.map P.dualTwistFunctor.h0 =
      AddMonoidHom.id (K₀ (H0 B)) - K₀.map (L.comp S).h0 := by
  letI : P.dualTwistFunctor.h0.CommShift ℤ := P.dualTwistH0CommShift
  letI : P.dualTwistFunctor.h0.IsTriangulated :=
    P.dualTwistH0IsTriangulated hLc hSc
  letI : (L.comp S).h0.CommShift ℤ :=
    DGFunctor.commShift _ (DGFunctor.preservesShifts _)
  letI : (L.comp S).h0.IsTriangulated :=
    DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
      (DGFunctor.preservesShifts _)
      (DGFunctor.PreservesChosenCones.comp hLc hSc)
  apply K₀.hom_ext
  intro X
  change K₀.of (H0 B) (P.dualTwistFunctor.h0.obj X) =
    K₀.of (H0 B) X - K₀.of (H0 B) ((L.comp S).h0.obj X)
  exact P.dualTwistFunctorK₀Of X

end Target

section Source

variable [IsPretriangulated A]

/-- The cotwist triangle gives `[C X] = [X] - [R S X]` in `K₀(H⁰ A)`. -/
theorem cotwistFunctorK₀Of (X : H0 A) :
    K₀.of (H0 A) (P.cotwistFunctor.h0.obj X) =
      K₀.of (H0 A) X - K₀.of (H0 A) ((S.comp R).h0.obj X) := by
  have h := K₀.of_triangle (H0 A) ((P.cotwistTriangleFunctor).obj X)
    (P.cotwistTriangleFunctor_obj_mem_distinguishedTriangles X)
  change K₀.of (H0 A) X =
    K₀.of (H0 A) (P.cotwistFunctor.h0.obj X) +
      K₀.of (H0 A) ((S.comp R).h0.obj X) at h
  rw [h]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- When `S` and `R` preserve chosen cones, the cotwist acts on `K₀` by the
identity minus the right-adjunction composite. -/
theorem cotwistFunctorK₀Map
    (hSc : DGFunctor.PreservesChosenCones S)
    (hRc : DGFunctor.PreservesChosenCones R) :
    letI : P.cotwistFunctor.h0.CommShift ℤ := P.cotwistH0CommShift
    letI : P.cotwistFunctor.h0.IsTriangulated :=
      P.cotwistH0IsTriangulated hSc hRc
    letI : (S.comp R).h0.CommShift ℤ :=
      DGFunctor.commShift _ (DGFunctor.preservesShifts _)
    letI : (S.comp R).h0.IsTriangulated :=
      DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
        (DGFunctor.preservesShifts _)
        (DGFunctor.PreservesChosenCones.comp hSc hRc)
    K₀.map P.cotwistFunctor.h0 =
      AddMonoidHom.id (K₀ (H0 A)) - K₀.map (S.comp R).h0 := by
  letI : P.cotwistFunctor.h0.CommShift ℤ := P.cotwistH0CommShift
  letI : P.cotwistFunctor.h0.IsTriangulated :=
    P.cotwistH0IsTriangulated hSc hRc
  letI : (S.comp R).h0.CommShift ℤ :=
    DGFunctor.commShift _ (DGFunctor.preservesShifts _)
  letI : (S.comp R).h0.IsTriangulated :=
    DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
      (DGFunctor.preservesShifts _)
      (DGFunctor.PreservesChosenCones.comp hSc hRc)
  apply K₀.hom_ext
  intro X
  change K₀.of (H0 A) (P.cotwistFunctor.h0.obj X) =
    K₀.of (H0 A) X - K₀.of (H0 A) ((S.comp R).h0.obj X)
  exact P.cotwistFunctorK₀Of X

/-- The dual-cotwist triangle gives `[C' X] = [X] - [L S X]` in
`K₀(H⁰ A)`. -/
theorem dualCotwistFunctorK₀Of (X : H0 A) :
    K₀.of (H0 A) (P.dualCotwistFunctor.h0.obj X) =
      K₀.of (H0 A) X - K₀.of (H0 A) ((S.comp L).h0.obj X) := by
  have h := K₀.of_triangle (H0 A) ((P.dualCotwistTriangleFunctor).obj X)
    (P.dualCotwistTriangleFunctor_obj_mem_distinguishedTriangles X)
  change K₀.of (H0 A) X =
    K₀.of (H0 A) ((S.comp L).h0.obj X) +
      K₀.of (H0 A) (P.dualCotwistFunctor.h0.obj X) at h
  rw [h]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- When `L` and `S` preserve chosen cones, the dual cotwist acts on `K₀` by
the identity minus the left-adjunction composite. -/
theorem dualCotwistFunctorK₀Map
    (hLc : DGFunctor.PreservesChosenCones L)
    (hSc : DGFunctor.PreservesChosenCones S) :
    letI : P.dualCotwistFunctor.h0.CommShift ℤ := P.dualCotwistH0CommShift
    letI : P.dualCotwistFunctor.h0.IsTriangulated :=
      P.dualCotwistH0IsTriangulated hLc hSc
    letI : (S.comp L).h0.CommShift ℤ :=
      DGFunctor.commShift _ (DGFunctor.preservesShifts _)
    letI : (S.comp L).h0.IsTriangulated :=
      DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
        (DGFunctor.preservesShifts _)
        (DGFunctor.PreservesChosenCones.comp hSc hLc)
    K₀.map P.dualCotwistFunctor.h0 =
      AddMonoidHom.id (K₀ (H0 A)) - K₀.map (S.comp L).h0 := by
  letI : P.dualCotwistFunctor.h0.CommShift ℤ := P.dualCotwistH0CommShift
  letI : P.dualCotwistFunctor.h0.IsTriangulated :=
    P.dualCotwistH0IsTriangulated hLc hSc
  letI : (S.comp L).h0.CommShift ℤ :=
    DGFunctor.commShift _ (DGFunctor.preservesShifts _)
  letI : (S.comp L).h0.IsTriangulated :=
    DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
      (DGFunctor.preservesShifts _)
      (DGFunctor.PreservesChosenCones.comp hSc hLc)
  apply K₀.hom_ext
  intro X
  change K₀.of (H0 A) (P.dualCotwistFunctor.h0.obj X) =
    K₀.of (H0 A) X - K₀.of (H0 A) ((S.comp L).h0.obj X)
  exact P.dualCotwistFunctorK₀Of X

end Source

end EnhancedAdjunctionCones

end CategoryTheory.Triangulated.SphericalTwist
