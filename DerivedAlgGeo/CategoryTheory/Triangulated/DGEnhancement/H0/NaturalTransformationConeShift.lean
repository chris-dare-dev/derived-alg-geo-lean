/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.NaturalTransformationShift
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.NaturalTransformationCone
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ShiftedFunctor

/-!
# The inverse-rotated first map of a dg cone triangle

For a closed degree-zero dg natural transformation `α : F ⟶ G`, its cone
triangle has connecting map `-fst` into `F[1]`.  Inverse rotation negates that
map once more and shifts it by `-1`, so its first map is the degree-one cone
projection `fst`, regraded to a closed degree-zero map `Cone(α)[-1] ⟶ F`.

This file records that identification as an equality of natural
transformations.  The source comparison is `shiftedFunctorH0Iso`: the dg
functor shift and the pointwise shift on `H⁰` are canonically isomorphic, not
definitionally identified as functors.  The shift cancellation used by inverse
rotation is Mathlib's `shiftFunctorCompIsoId`, whose component computation is
exposed by `H0.shiftFunctorCompIsoId_hom_app`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated

namespace DGFunctor.HomogeneousNatTrans.ConeData

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]
  [IsPretriangulated D] {F G : DGFunctor C D} {α : HomogeneousNatTrans F G 0}
  (K : ConeData α) (hα : IsClosed α)

/-- The first morphisms of the objectwise inverse-rotated cone triangles,
assembled into a natural transformation. -/
noncomputable def inverseRotateFirstH0 :
    K.functor.h0 ⋙ shiftFunctor (H0 D) (-1 : ℤ) ⟶ F.h0 where
  app X := (K.triangleObj hα (H0.of C X)).invRotate.mor₁
  naturality _ _ f :=
    ((Pretriangulated.invRotate (H0 D)).map
      ((K.triangleFunctor hα).map f)).comm₁.symm

/-- The closed degree-one cone projection, source-regraded to a degree-zero
map out of the selected `[-1]` shift and descended to `H⁰`. -/
noncomputable def shiftedFstH0 :
    (K.functor.shiftedFunctor (-1 : ℤ)).h0 ⟶ F.h0 :=
  HomogeneousNatTrans.h0
    (HomogeneousNatTrans.sourceShiftEquiv K.functor F
      (-1 : ℤ) 1 0 (by omega) K.fst)
    ((HomogeneousNatTrans.sourceShiftEquiv_isClosed_iff K.functor F
      (-1 : ℤ) 1 0 (by omega) K.fst).2 K.fst_isClosed)

private lemma shiftedToShift_comp_cancel (X : C) :
    dgComp 0 0 0 (by omega)
        (IsShiftBy.mapShift
          (IsPretriangulated.shiftWitness D (K.obj X) (-1))
          (IsPretriangulated.shiftWitness D
            (IsPretriangulated.shiftObj D (F.obj X) 1) (-1))
          ((K.isCone X).toShift
            (IsPretriangulated.shiftWitness D (F.obj X) 1)))
        (IsShiftBy.compare
          (H0.shiftCompWitness' D (F.obj X) 1 (-1) 0 (by omega))
          (IsShiftBy.self (F.obj X))) =
      dgComp (-1) 1 0 (by omega)
        (IsPretriangulated.shiftWitness D (K.obj X) (-1)).inv
        (HomogeneousNatTrans.app K.fst X) := by
  rw [IsShiftBy.compare]
  change dgComp 0 0 0 (by omega)
      (IsShiftBy.mapShift
        (IsPretriangulated.shiftWitness D (K.obj X) (-1))
        (IsPretriangulated.shiftWitness D
          (IsPretriangulated.shiftObj D (F.obj X) 1) (-1))
        ((K.isCone X).toShift
          (IsPretriangulated.shiftWitness D (F.obj X) 1)))
      (dgComp 0 0 0 (by omega)
        (H0.shiftCompWitness' D (F.obj X) 1 (-1) 0 (by omega)).inv
        (dgId (F.obj X))) = _
  rw [dgComp_id, H0.shiftCompWitness']
  have hcompInv := IsShiftBy.comp'_inv
    (IsPretriangulated.shiftWitness D (F.obj X) 1)
    (IsPretriangulated.shiftWitness D
      (IsPretriangulated.shiftObj D (F.obj X) 1) (-1)) 0 (by omega)
  have hmap := IsShiftBy.shiftMap_comp_inv
    (IsPretriangulated.shiftWitness D (K.obj X) (-1))
    (IsPretriangulated.shiftWitness D
      (IsPretriangulated.shiftObj D (F.obj X) 1) (-1))
    0 (-1) (by omega) (by omega)
    ((K.isCone X).toShift
      (IsPretriangulated.shiftWitness D (F.obj X) 1))
  calc
    _ = dgComp 0 0 0 (by omega)
          (IsShiftBy.mapShift
            (IsPretriangulated.shiftWitness D (K.obj X) (-1))
            (IsPretriangulated.shiftWitness D
              (IsPretriangulated.shiftObj D (F.obj X) 1) (-1))
            ((K.isCone X).toShift
              (IsPretriangulated.shiftWitness D (F.obj X) 1)))
          (dgComp (-1) 1 0 (by omega)
            (IsPretriangulated.shiftWitness D
              (IsPretriangulated.shiftObj D (F.obj X) 1) (-1)).inv
            (IsPretriangulated.shiftWitness D (F.obj X) 1).inv) :=
      congrArg _ hcompInv.symm
    _ = dgComp (-1) 1 0 (by omega)
          (dgComp 0 (-1) (-1) (by omega)
            (IsShiftBy.mapShift
              (IsPretriangulated.shiftWitness D (K.obj X) (-1))
              (IsPretriangulated.shiftWitness D
                (IsPretriangulated.shiftObj D (F.obj X) 1) (-1))
              ((K.isCone X).toShift
                (IsPretriangulated.shiftWitness D (F.obj X) 1)))
            (IsPretriangulated.shiftWitness D
              (IsPretriangulated.shiftObj D (F.obj X) 1) (-1)).inv)
          (IsPretriangulated.shiftWitness D (F.obj X) 1).inv :=
      (dgComp_assoc 0 (-1) 1 (-1) 0 0
        (by omega) (by omega) (by omega)
        (IsShiftBy.mapShift
          (IsPretriangulated.shiftWitness D (K.obj X) (-1))
          (IsPretriangulated.shiftWitness D
            (IsPretriangulated.shiftObj D (F.obj X) 1) (-1))
          ((K.isCone X).toShift
            (IsPretriangulated.shiftWitness D (F.obj X) 1)))
        (IsPretriangulated.shiftWitness D
          (IsPretriangulated.shiftObj D (F.obj X) 1) (-1)).inv
        (IsPretriangulated.shiftWitness D (F.obj X) 1).inv).symm
    _ = dgComp (-1) 1 0 (by omega)
          (dgComp (-1) 0 (-1) (by omega)
            (IsPretriangulated.shiftWitness D (K.obj X) (-1)).inv
            ((K.isCone X).toShift
              (IsPretriangulated.shiftWitness D (F.obj X) 1)))
          (IsPretriangulated.shiftWitness D (F.obj X) 1).inv :=
      congrArg
        (fun z => dgComp (-1) 1 0 (by omega) z
          (IsPretriangulated.shiftWitness D (F.obj X) 1).inv) hmap
    _ = _ := by
      rw [dgComp_assoc (-1) 0 1 (-1) 1 0
          (by omega) (by omega) (by omega),
        IsConeOf.toShift,
        dgComp_assoc 1 (-1) 1 0 0 1
          (by omega) (by omega) (by omega),
        IsShiftBy.hom_inv, dgComp_id, K.fst_app]

/-- **Inverse rotation reads the cone projection through source regrading.**

The cone triangle and inverse rotation each contribute one minus sign.  After
they cancel, the inverse-rotation shift comparison cancels the selected `[1]`
witness in the connecting map, leaving the selected `[-1]` inverse followed
by `fst`. -/
theorem inverseRotateFirstH0_app_eq_shiftedFstH0 (X : H0 C) :
    (K.inverseRotateFirstH0 hα).app X = (K.shiftedFstH0).app X := by
  change (K.triangleObj hα (H0.of C X)).invRotate.mor₁ = _
  rw [Triangle.invRotate_mor₁]
  change -((shiftFunctor (H0 D) (-1 : ℤ)).map
      (K.triangleObj hα (H0.of C X)).mor₃) ≫ _ = _
  change -((shiftFunctor (H0 D) (-1 : ℤ)).map
      (H0.coneTriangle
        ⟨app α (H0.of C X), hα.app_mem_cocycles (H0.of C X)⟩
        (K.isCone (H0.of C X))).mor₃) ≫ _ = _
  rw [H0.coneTriangle_mor₃]
  let f : (show H0 D from K.obj (H0.of C X)) ⟶
      (show H0 D from
        IsPretriangulated.shiftObj D (F.obj (H0.of C X)) 1) :=
    H0.homMk (C := D) ⟨(K.isCone (H0.of C X)).toShift
      (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) 1),
      (K.isCone (H0.of C X)).toShift_mem_cocycles _⟩
  let c := (shiftFunctorCompIsoId (H0 D) 1 (-1) (by omega)).hom.app
    (show H0 D from F.obj (H0.of C X))
  have hmapNeg : (shiftFunctor (H0 D) (-1 : ℤ)).map (-f) =
      -(shiftFunctor (H0 D) (-1 : ℤ)).map f :=
    Functor.map_neg _
  have hsign : -((shiftFunctor (H0 D) (-1 : ℤ)).map (-f) ≫ c) =
      (shiftFunctor (H0 D) (-1 : ℤ)).map f ≫ c :=
    (Preadditive.neg_comp _ _).symm.trans
      (congrArg (fun z => z ≫ c)
        ((congrArg Neg.neg hmapNeg).trans (neg_neg _)))
  have hshift := H0.shiftFunctor_map_mk (C := D) (-1)
    ⟨(K.isCone (H0.of C X)).toShift
      (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) 1),
      (K.isCone (H0.of C X)).toShift_mem_cocycles _⟩
  have hcancel := H0.shiftFunctorCompIsoId_hom_app (C := D)
    1 (-1) (by omega) (show H0 D from F.obj (H0.of C X))
  have hpositive : (shiftFunctor (H0 D) (-1 : ℤ)).map f ≫ c =
      (K.shiftedFstH0).app X := by
    calc
      _ = H0.homMk (C := D) ⟨IsShiftBy.mapShift
            (IsPretriangulated.shiftWitness D (K.obj (H0.of C X)) (-1))
            (IsPretriangulated.shiftWitness D
              (IsPretriangulated.shiftObj D (F.obj (H0.of C X)) 1) (-1))
            ((K.isCone (H0.of C X)).toShift
              (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) 1)),
            IsShiftBy.mapShift_mem_cocycles _ _
              ((K.isCone (H0.of C X)).toShift_mem_cocycles _)⟩ ≫
          H0.homMk (C := D) ⟨IsShiftBy.compare
            (H0.shiftCompWitness' D (F.obj (H0.of C X)) 1 (-1) 0 (by omega))
            (IsShiftBy.self (F.obj (H0.of C X))),
            IsShiftBy.compare_mem_cocycles _ _⟩ :=
        congrArg₂ (fun a b => a ≫ b) hshift hcancel
      _ = H0.homMk (C := D) ⟨dgComp 0 0 0 (by omega)
            (IsShiftBy.mapShift
              (IsPretriangulated.shiftWitness D (K.obj (H0.of C X)) (-1))
              (IsPretriangulated.shiftWitness D
                (IsPretriangulated.shiftObj D (F.obj (H0.of C X)) 1) (-1))
              ((K.isCone (H0.of C X)).toShift
                (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) 1)))
            (IsShiftBy.compare
              (H0.shiftCompWitness' D (F.obj (H0.of C X)) 1 (-1) 0 (by omega))
              (IsShiftBy.self (F.obj (H0.of C X)))),
            dgComp_closed (by omega) (by omega)
              (IsShiftBy.mapShift_mem_cocycles _ _
                ((K.isCone (H0.of C X)).toShift_mem_cocycles _))
              (IsShiftBy.compare_mem_cocycles _ _)⟩ :=
        H0.homMk_comp _ _
      _ = H0.homMk (C := D) ⟨dgComp (-1) 1 0 (by omega)
            (IsPretriangulated.shiftWitness D (K.obj (H0.of C X)) (-1)).inv
            (HomogeneousNatTrans.app K.fst (H0.of C X)),
            dgComp_closed (by omega) (by omega)
              (IsShiftBy.inv_closed _)
              (K.fst_isClosed.app_d (H0.of C X))⟩ :=
        congrArg (fun z => H0.homMk (C := D) z)
          (Subtype.ext (K.shiftedToShift_comp_cancel (H0.of C X)))
      _ = _ :=
        congrArg (fun z => H0.homMk (C := D) z)
          (Subtype.ext
            (HomogeneousNatTrans.sourceShiftEquiv_apply_app
              K.functor F (-1) 1 0 (by omega) K.fst (H0.of C X)).symm)
  exact hsign.trans hpositive

/-- The inverse-rotated first map is the `H⁰` image of the regraded dg cone
projection, after comparing the dg functor shift with the pointwise shift. -/
theorem shiftedFstH0_eq :
    K.shiftedFstH0 =
      (K.functor.shiftedFunctorH0Iso (-1)).hom ≫
        K.inverseRotateFirstH0 hα := by
  ext X
  change (K.shiftedFstH0).app X =
    (K.functor.shiftedFunctorH0Iso (-1)).hom.app X ≫
      (K.inverseRotateFirstH0 hα).app X
  have hIso := DGFunctor.shiftedFunctorH0Iso_hom_app
    K.functor (-1) X
  have hcomp := congrArg
    (fun z => z ≫ (K.inverseRotateFirstH0 hα).app X) hIso
  exact (K.inverseRotateFirstH0_app_eq_shiftedFstH0 hα X).symm |>.trans
    ((Category.id_comp _).symm.trans hcomp.symm)

end DGFunctor.HomogeneousNatTrans.ConeData

end CategoryTheory
