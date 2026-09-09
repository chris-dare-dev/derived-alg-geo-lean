/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Functor
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Triangle

/-!
# Transporting dg-functor capabilities to `H⁰`

`DGFunctor.PreservesShifts` and `DGFunctor.PreservesChosenCones` are dg-level
capabilities, owned by `Algebra/Homology/DGCategory/Pretriangulated/Functor.lean`.
This file spends them on the ordinary functor `H⁰(F)`: the chosen shift
witnesses assemble into a `CommShift`, and cone-generator preservation makes
that functor triangulated.

`H0/Triangle.lean` owns the distinguished triangles of `H⁰` and the
pretriangulated instance; everything here consumes them, which is why the
dependency runs this way rather than the other.  Both files sit under the
`H0` umbrella, so no consumer has to know which of the two a name comes from.

## The `backward.isDefEq.respectTransparency` options are load-bearing

Five declarations below carry `set_option backward.isDefEq.respectTransparency
false`.  They were tried without it: `commShift` fails with a type mismatch
whose two sides print identically, and
`preservesConeTriangles_of_preservesChosenCones` fails to find `𝟙` under
`Functor.map`.  Both are the shift and cone witnesses being compared at
`instances` transparency, which does not unfold `H0`, `IsPretriangulated.shiftObj`
or the chosen witnesses.  Removing them needs those comparisons restated
through explicit `show` steps, not a tactic swap.

The two uses in `Triangulated/FullSubcategory.lean` are the same story.  Note
that until this file was given its own umbrella entry nothing imported it, so a
green build was not evidence that these proofs still worked.

## Why the cone-generator property is the right hypothesis

`H⁰`'s distinguished triangles are by definition those isomorphic to a dg cone
triangle, so a functor is triangulated as soon as it sends *cone* triangles to
distinguished triangles.  `PreservesConeTriangles` is that condition and
nothing more; `preservesConeTriangles_of_preservesChosenCones` derives it from
the strong dg-level capability, and the two `isTriangulated_of_…` results
close the loop.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Limits Pretriangulated

namespace DGFunctor

variable {C D : Type u} [DGCategory.{v} C] [DGCategory.{v} D]

set_option backward.isDefEq.respectTransparency false in
/-- The shift comparison induced on `H⁰` by dg-level shift preservation. -/
noncomputable def shiftCommIso (F : DGFunctor C D) (hF : PreservesShifts F) (n : ℤ)
    [IsPretriangulated C] [IsPretriangulated D] :
    CategoryTheory.shiftFunctor (H0 C) n ⋙ F.h0 ≅
      F.h0 ⋙ CategoryTheory.shiftFunctor (H0 D) n :=
  NatIso.ofComponents
    (fun X => H0.compareIso (C := D)
      (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) n))
      (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) n))
    (by
      intro X Y f
      induction f using Quotient.ind with
      | _ f =>
        change
          H0.homMk (C := D)
              ⟨F.map 0 (IsShiftBy.mapShift
                (IsPretriangulated.shiftWitness C (H0.of C X) n)
                (IsPretriangulated.shiftWitness C (H0.of C Y) n) f.1), _⟩ ≫
            H0.homMk (C := D)
              ⟨IsShiftBy.compare
                (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C Y) n))
                (IsPretriangulated.shiftWitness D (F.obj (H0.of C Y)) n), _⟩ =
          H0.homMk (C := D)
              ⟨IsShiftBy.compare
                (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) n))
                (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) n), _⟩ ≫
            H0.homMk (C := D)
              ⟨IsShiftBy.mapShift
                (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) n)
                (IsPretriangulated.shiftWitness D (F.obj (H0.of C Y)) n)
                (F.map 0 f.1), _⟩
        refine (H0.homMk_comp (C := D) _ _).trans ?_
        refine Eq.trans ?_ (H0.homMk_comp (C := D) _ _).symm
        refine congrArg _ (Subtype.ext ?_)
        refine (congrArg (fun z => dgComp 0 0 0 (by omega) z
            (IsShiftBy.compare
              (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C Y) n))
              (IsPretriangulated.shiftWitness D (F.obj (H0.of C Y)) n)))
          (DGFunctor.map_mapShift hF
            (IsPretriangulated.shiftWitness C (H0.of C X) n)
            (IsPretriangulated.shiftWitness C (H0.of C Y) n) f.1)).trans ?_
        exact IsShiftBy.mapShift_compare
          (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) n))
          (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) n)
          (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C Y) n))
          (IsPretriangulated.shiftWitness D (F.obj (H0.of C Y)) n)
          (F.map 0 f.1))

set_option backward.isDefEq.respectTransparency false in
lemma shiftCommIso_zero_hom_app (F : DGFunctor C D)
    [IsPretriangulated C] [IsPretriangulated D] (hF : PreservesShifts F) (X : H0 C) :
    (shiftCommIso F hF 0).hom.app X =
      F.h0.map ((H0.shiftFunctorZeroIso C).hom.app X) ≫
        (H0.shiftFunctorZeroIso D).inv.app (F.h0.obj X) := by
  dsimp [shiftCommIso, H0.shiftFunctorZeroIso, H0.compareIso]
  change H0.homMk (C := D) _ =
    F.h0.map (H0.homMk (C := C) _) ≫ H0.homMk (C := D) _
  change H0.homMk (C := D) _ =
    H0.homMk (C := D) _ ≫ H0.homMk (C := D) _
  rw [H0.homMk_comp]
  refine congrArg _ (Subtype.ext ?_)
  change
    IsShiftBy.compare
        (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) 0))
        (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) 0) =
      dgComp 0 0 0 (by omega)
        (F.map 0 (IsShiftBy.compare
          (IsPretriangulated.shiftWitness C (H0.of C X) 0)
          (IsShiftBy.self (H0.of C X))))
        (IsShiftBy.compare
          (IsShiftBy.self (F.obj (H0.of C X)))
          (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) 0))
  have hself :
      (hF.mapShift (IsShiftBy.self (H0.of C X))).hom =
        (IsShiftBy.self (F.obj (H0.of C X))).hom := by
    rw [hF.mapShift_hom]
    simpa [IsShiftBy.self] using F.map_id (H0.of C X)
  calc
    IsShiftBy.compare
          (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) 0))
          (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) 0) =
        dgComp 0 0 0 (by omega)
          (IsShiftBy.compare
            (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) 0))
            (hF.mapShift (IsShiftBy.self (H0.of C X))))
          (IsShiftBy.compare
            (hF.mapShift (IsShiftBy.self (H0.of C X)))
            (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) 0)) :=
      (IsShiftBy.compare_trans _ _ _).symm
    _ = dgComp 0 0 0 (by omega)
          (F.map 0 (IsShiftBy.compare
            (IsPretriangulated.shiftWitness C (H0.of C X) 0)
            (IsShiftBy.self (H0.of C X))))
          (IsShiftBy.compare
            (IsShiftBy.self (F.obj (H0.of C X)))
            (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) 0)) := by
      rw [← DGFunctor.map_compare hF
        (IsPretriangulated.shiftWitness C (H0.of C X) 0)
        (IsShiftBy.self (H0.of C X)),
        IsShiftBy.compare_congr_left
          (hF.mapShift (IsShiftBy.self (H0.of C X)))
          (IsShiftBy.self (F.obj (H0.of C X)))
          (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) 0) hself]

set_option backward.isDefEq.respectTransparency false in
lemma shiftCommIso_add_hom_app (F : DGFunctor C D)
    [IsPretriangulated C] [IsPretriangulated D] (hF : PreservesShifts F)
    (a b : ℤ) (X : H0 C) :
    (shiftCommIso F hF (a + b)).hom.app X =
      F.h0.map ((H0.shiftFunctorAddIso C a b).hom.app X) ≫
        (shiftCommIso F hF b).hom.app ((H0.shiftFunctor C a).obj X) ≫
          (H0.shiftFunctor D b).map ((shiftCommIso F hF a).hom.app X) ≫
            (H0.shiftFunctorAddIso D a b).inv.app (F.h0.obj X) := by
  dsimp [shiftCommIso, H0.shiftFunctorAddIso, H0.shiftFunctorAddIso', H0.compareIso,
    H0.shiftFunctor]
  change H0.homMk (C := D) _ =
    H0.homMk (C := D) _ ≫ H0.homMk (C := D) _ ≫
      H0.homMk (C := D) _ ≫ H0.homMk (C := D) _
  rw [H0.homMk_comp, H0.homMk_comp, H0.homMk_comp]
  refine congrArg _ (Subtype.ext ?_)
  change
    IsShiftBy.compare
        (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) (a + b)))
        (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) (a + b)) =
      dgComp 0 0 0 (by omega)
        (F.map 0 (IsShiftBy.compare
          (IsPretriangulated.shiftWitness C (H0.of C X) (a + b))
          (H0.shiftCompWitness C (H0.of C X) a b)))
        (dgComp 0 0 0 (by omega)
          (IsShiftBy.compare
            (hF.mapShift (IsPretriangulated.shiftWitness C
              (IsPretriangulated.shiftObj C (H0.of C X) a) b))
            (IsPretriangulated.shiftWitness D
              (F.obj (IsPretriangulated.shiftObj C (H0.of C X) a)) b))
          (dgComp 0 0 0 (by omega)
            (IsShiftBy.mapShift
              (IsPretriangulated.shiftWitness D
                (F.obj (IsPretriangulated.shiftObj C (H0.of C X) a)) b)
              (IsPretriangulated.shiftWitness D
                (IsPretriangulated.shiftObj D (F.obj (H0.of C X)) a) b)
              (IsShiftBy.compare
                (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) a))
                (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) a)))
            (IsShiftBy.compare
              (H0.shiftCompWitness D (F.obj (H0.of C X)) a b)
              (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) (a + b)))))
  have hcomp :
      (hF.mapShift (H0.shiftCompWitness C (H0.of C X) a b)).hom =
        (IsShiftBy.comp'
          (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) a))
          (hF.mapShift (IsPretriangulated.shiftWitness C
            (IsPretriangulated.shiftObj C (H0.of C X) a) b))
          (a + b) rfl).hom := by
    rw [hF.mapShift_hom (s := H0.shiftCompWitness C (H0.of C X) a b)]
    change F.map (-(a + b))
          (dgComp (-a) (-b) (-(a + b)) (by omega)
            (IsPretriangulated.shiftWitness C (H0.of C X) a).hom
            (IsPretriangulated.shiftWitness C
              (IsPretriangulated.shiftObj C (H0.of C X) a) b).hom) =
        dgComp (-a) (-b) (-(a + b)) (by omega)
          (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) a)).hom
          (hF.mapShift (IsPretriangulated.shiftWitness C
            (IsPretriangulated.shiftObj C (H0.of C X) a) b)).hom
    rw [F.map_comp, hF.mapShift_hom, hF.mapShift_hom]
  symm
  rw [DGFunctor.map_compare hF
        (IsPretriangulated.shiftWitness C (H0.of C X) (a + b))
        (H0.shiftCompWitness C (H0.of C X) a b),
      IsShiftBy.compare_congr
        (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) (a + b)))
        (hF.mapShift (H0.shiftCompWitness C (H0.of C X) a b))
        (IsShiftBy.comp'
          (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) a))
          (hF.mapShift (IsPretriangulated.shiftWitness C
            (IsPretriangulated.shiftObj C (H0.of C X) a) b))
          (a + b) rfl) hcomp]
  have hBC :
      dgComp 0 0 0 (by omega)
          (IsShiftBy.compare
            (hF.mapShift (IsPretriangulated.shiftWitness C
              (IsPretriangulated.shiftObj C (H0.of C X) a) b))
            (IsPretriangulated.shiftWitness D
              (F.obj (IsPretriangulated.shiftObj C (H0.of C X) a)) b))
          (dgComp 0 0 0 (by omega)
            (IsShiftBy.mapShift
              (IsPretriangulated.shiftWitness D
                (F.obj (IsPretriangulated.shiftObj C (H0.of C X) a)) b)
              (IsPretriangulated.shiftWitness D
                (IsPretriangulated.shiftObj D (F.obj (H0.of C X)) a) b)
              (IsShiftBy.compare
                (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) a))
                (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) a)))
            (IsShiftBy.compare
              (H0.shiftCompWitness D (F.obj (H0.of C X)) a b)
              (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) (a + b)))) =
        dgComp 0 0 0 (by omega)
          (IsShiftBy.mapShift
            (hF.mapShift (IsPretriangulated.shiftWitness C
              (IsPretriangulated.shiftObj C (H0.of C X) a) b))
            (IsPretriangulated.shiftWitness D
              (IsPretriangulated.shiftObj D (F.obj (H0.of C X)) a) b)
            (IsShiftBy.compare
              (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) a))
              (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) a)))
          (IsShiftBy.compare
            (H0.shiftCompWitness D (F.obj (H0.of C X)) a b)
            (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) (a + b))) := by
    rw [← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega),
      ← IsShiftBy.mapShift_compare
        (hF.mapShift (IsPretriangulated.shiftWitness C
          (IsPretriangulated.shiftObj C (H0.of C X) a) b))
        (IsPretriangulated.shiftWitness D
          (F.obj (IsPretriangulated.shiftObj C (H0.of C X) a)) b)
        (IsPretriangulated.shiftWitness D
          (IsPretriangulated.shiftObj D (F.obj (H0.of C X)) a) b)
        (IsPretriangulated.shiftWitness D
          (IsPretriangulated.shiftObj D (F.obj (H0.of C X)) a) b)
        (IsShiftBy.compare
          (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) a))
          (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) a)),
      IsShiftBy.compare_self, dgComp_id]
  rw [hBC]
  rw [IsShiftBy.mapShift_compare_comp'
    (hF.mapShift (IsPretriangulated.shiftWitness C (H0.of C X) a))
    (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) a)
    (hF.mapShift (IsPretriangulated.shiftWitness C
      (IsPretriangulated.shiftObj C (H0.of C X) a) b))
    (IsPretriangulated.shiftWitness D
      (IsPretriangulated.shiftObj D (F.obj (H0.of C X)) a) b)
    (a + b) rfl]
  have htarget :
      (H0.shiftCompWitness D (F.obj (H0.of C X)) a b).hom =
        (IsShiftBy.comp'
          (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) a)
          (IsPretriangulated.shiftWitness D
            (IsPretriangulated.shiftObj D (F.obj (H0.of C X)) a) b)
          (a + b) rfl).hom := rfl
  rw [IsShiftBy.compare_congr_left
        (H0.shiftCompWitness D (F.obj (H0.of C X)) a b)
        (IsShiftBy.comp'
          (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) a)
          (IsPretriangulated.shiftWitness D
            (IsPretriangulated.shiftObj D (F.obj (H0.of C X)) a) b)
          (a + b) rfl)
        (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) (a + b)) htarget,
      IsShiftBy.compare_trans, IsShiftBy.compare_trans]

set_option backward.isDefEq.respectTransparency false in
/-- The dg-level shift-preservation data supplies the coherent shift structure
required by the ordinary functor `H⁰(F)`. -/
@[reducible]
noncomputable def commShift (F : DGFunctor C D)
    [IsPretriangulated C] [IsPretriangulated D] (hF : PreservesShifts F) :
    F.h0.CommShift ℤ where
  commShiftIso := fun n => shiftCommIso F hF n
  commShiftIso_zero := by
    ext X
    rw [Functor.CommShift.isoZero_hom_app, H0.shiftFunctorZero_eq]
    exact shiftCommIso_zero_hom_app F hF X
  commShiftIso_add a b := by
    ext X
    rw [Functor.CommShift.isoAdd_hom_app, H0.shiftFunctorAdd_eq]
    exact shiftCommIso_add_hom_app F hF a b X

/-- Preservation data for the cone generators of `H⁰`.

This is the reusable exactness seam for a dg functor: it asks that the image of
each chosen dg cone triangle be isomorphic to a cone triangle in the target.
It does not assert that an arbitrary dg functor has this property, nor does it
duplicate `Functor.IsTriangulated` as a field. -/
structure PreservesConeTriangles (F : DGFunctor C D)
    [IsPretriangulated C] [IsPretriangulated D] [F.h0.CommShift ℤ] : Prop where
  /-- The image of a dg cone triangle is a target cone triangle up to triangle
  isomorphism. -/
  map_cone {X Y : C} (f : cocycles X Y) {Z : C} (hc : IsConeOf f.1 Z) :
    ∃ (Z' : D) (hc' : IsConeOf (F.map 0 f.1) Z'),
      Nonempty
        (F.h0.mapTriangle.obj (H0.coneTriangle (C := C) f hc) ≅
          H0.coneTriangle (C := D)
            (⟨F.map 0 f.1, F.map_mem_cocycles f.2⟩ :
              cocycles (F.obj X) (F.obj Y)) hc')

set_option backward.isDefEq.respectTransparency false in
/-- Strong dg-level preservation of chosen shifts and cones implies the weak
cone-generator preservation property needed for exactness on `H⁰`.

The target cone is the image object itself.  The comparison triangle has
identity components: compatibility of the first two arrows is forced by the
stored image inclusions, while compatibility of the connecting arrow is
derived from uniqueness of cone projections and the canonical shift
comparison. -/
theorem preservesConeTriangles_of_preservesChosenCones
    (F : DGFunctor C D) [IsPretriangulated C] [IsPretriangulated D]
    (hShift : PreservesShifts F) (hCone : PreservesChosenCones F) :
    letI : F.h0.CommShift ℤ := commShift F hShift
    PreservesConeTriangles F := by
  letI : F.h0.CommShift ℤ := commShift F hShift
  constructor
  intro X Y f Z hc
  refine ⟨F.obj Z, hCone.mapCone hc, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · refine (Category.comp_id _).trans ?_
    refine Eq.trans ?_ (Category.id_comp _).symm
    change F.h0.map (H0.homMk (C := C) ⟨hc.inr, hc.inr_mem_cocycles⟩) =
      H0.homMk (C := D)
        ⟨(hCone.mapCone hc).inr, (hCone.mapCone hc).inr_mem_cocycles⟩
    exact (F.h0_map_mk
      (X := (show H0 C from Y)) (Y := (show H0 C from Z))
      ⟨hc.inr, hc.inr_mem_cocycles⟩).trans
        (congrArg _ (Subtype.ext (hCone.mapCone_inr hc).symm))
  · let sC := IsPretriangulated.shiftWitness C X 1
    let sD := IsPretriangulated.shiftWitness D (F.obj X) 1
    simp only [Iso.refl_hom]
    rw [Functor.map_id]
    refine (Category.comp_id _).trans ?_
    refine Eq.trans ?_ (Category.id_comp _).symm
    change F.h0.map (-H0.homMk (C := C)
          ⟨hc.toShift sC, hc.toShift_mem_cocycles sC⟩) ≫
        H0.homMk (C := D)
          ⟨IsShiftBy.compare (hShift.mapShift sC) sD,
            IsShiftBy.compare_mem_cocycles _ _⟩ =
      -H0.homMk (C := D)
        ⟨(hCone.mapCone hc).toShift sD,
          (hCone.mapCone hc).toShift_mem_cocycles sD⟩
    have hmap : F.h0.map (-H0.homMk (C := C)
          ⟨hc.toShift sC, hc.toShift_mem_cocycles sC⟩) =
        -H0.homMk (C := D)
          ⟨F.map 0 (hc.toShift sC), F.map_mem_cocycles (hc.toShift_mem_cocycles sC)⟩ := by
      calc
        F.h0.map (-H0.homMk (C := C)
            ⟨hc.toShift sC, hc.toShift_mem_cocycles sC⟩) =
            F.h0.map (H0.homMk (C := C)
              (-⟨hc.toShift sC, hc.toShift_mem_cocycles sC⟩)) := by
                rw [H0.homMk_neg]
        _ = H0.homMk (C := D)
              ⟨F.map 0 (-hc.toShift sC),
                F.map_mem_cocycles
                  ((-⟨hc.toShift sC, hc.toShift_mem_cocycles sC⟩ :
                    cocycles Z (IsPretriangulated.shiftObj C X 1)).2)⟩ :=
              F.h0_map_mk
                (X := (show H0 C from Z))
                (Y := (show H0 C from IsPretriangulated.shiftObj C X 1)) _
        _ = -H0.homMk (C := D)
              ⟨F.map 0 (hc.toShift sC),
                F.map_mem_cocycles (hc.toShift_mem_cocycles sC)⟩ := by
              rw [← H0.homMk_neg]
              exact congrArg _ (Subtype.ext
                (map_neg (F.map 0) (hc.toShift sC)))
    rw [hmap, Preadditive.neg_comp, H0.homMk_comp]
    refine congrArg Neg.neg (congrArg _ (Subtype.ext ?_))
    exact (congrArg (fun q => dgComp 0 0 0 (by omega) q
      (IsShiftBy.compare (hShift.mapShift sC) sD))
        (hCone.mapCone_toShift hShift hc sC)).trans
      ((hCone.mapCone hc).toShift_comp_compare (hShift.mapShift sC) sD)

/-- A dg functor with cone-generator preservation induces a triangulated
functor on `H⁰`. The proof is the generator argument built into the definition
of `H⁰.distinguishedTriangles`, followed by closure under triangle isomorphism. -/
theorem isTriangulated_of_preservesConeTriangles
    (F : DGFunctor C D) [IsPretriangulated C] [IsPretriangulated D]
    [F.h0.CommShift ℤ] (hF : PreservesConeTriangles F) :
    F.h0.IsTriangulated := by
  constructor
  intro T hT
  rw [H0.mem_distTriang_iff C] at hT
  rw [H0.mem_distTriang_iff D]
  obtain ⟨X, Y, f, Z, hc, ⟨e⟩⟩ := hT
  obtain ⟨Z', hc', ⟨e'⟩⟩ := hF.map_cone f hc
  exact H0.isomorphic_distinguished _
    (H0.coneTriangle_mem
      (⟨F.map 0 f.1, F.map_mem_cocycles f.2⟩ :
        cocycles (F.obj X) (F.obj Y)) hc') _
    (F.h0.mapTriangle.mapIso e ≪≫ e')

/-- A shift-preserving dg functor needs only cone-generator preservation in
addition to its canonical shift structure to induce a triangulated functor on
`H⁰`. The explicit instance argument keeps callers from having to reproduce
the `commShift` construction at every use site. -/
theorem isTriangulated_of_preservesShifts_and_coneTriangles
    (F : DGFunctor C D) [IsPretriangulated C] [IsPretriangulated D]
    (hShift : PreservesShifts F)
    (hCone : @PreservesConeTriangles C D _ _ F _ _ (commShift F hShift)) :
    letI : F.h0.CommShift ℤ := commShift F hShift
    F.h0.IsTriangulated := by
  letI : F.h0.CommShift ℤ := commShift F hShift
  exact isTriangulated_of_preservesConeTriangles F hCone

/-- The strong composable dg capabilities are sufficient to make `H⁰(F)` a
triangulated functor.  The weak cone-generator proposition is derived
internally and does not have to be supplied by callers. -/
theorem isTriangulated_of_preservesShifts_and_chosenCones
    (F : DGFunctor C D) [IsPretriangulated C] [IsPretriangulated D]
    (hShift : PreservesShifts F) (hCone : PreservesChosenCones F) :
    letI : F.h0.CommShift ℤ := commShift F hShift
    F.h0.IsTriangulated := by
  letI : F.h0.CommShift ℤ := commShift F hShift
  exact isTriangulated_of_preservesConeTriangles F
    (preservesConeTriangles_of_preservesChosenCones F hShift hCone)

end DGFunctor

end CategoryTheory
