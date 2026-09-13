/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.FunctorCategory
import DerivedAlgGeo.CategoryTheory.Shift.CommShift
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Functor
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.FunctorTransport
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Shift
import DerivedAlgGeo.CategoryTheory.Triangulated.ShiftFunctor

/-!
# The dg shift of a functor computes the `H⁰` shift

`DGFunctor.shiftedFunctor` shifts a dg functor by `n`, and `H0.shiftFunctor`
shifts an object of `H⁰` by `n`.  Both are built from the same choice, namely
`IsPretriangulated.exists_shift`, so they agree:

`H⁰ (F[n]) = H⁰ F ⋙ (-)[n]`,

The object equality is `rfl`; the morphism equality is the second computation
lemma below.  The resulting functor equality and its natural-isomorphism
wrapper make ordinary categorical properties such as equivalence and
triangulatedness reusable for shifted dg functors.

## Why it is not just `rfl` on morphisms

Two things differ, and both are harmless.  The shifted functor carries the
Koszul sign `(-1)^(n p)`, which at the degree `p = 0` of an `H⁰` morphism is
`+1`.  And the shifted functor's action is `IsShiftBy.shiftMap` at degree
zero, while the `H⁰` shift's is `IsShiftBy.mapShift`; those are the same map,
but `shiftMap` indexes its middle composite by `n + 0` where `mapShift` uses
`n`, and for a variable `n` that is only propositionally an equality.
`IsShiftBy.shiftMap_zero_eq_mapShift` crosses it.

## What this is for

It makes "the cotwist is the shift of the cone functor" a statement about the
dg functor rather than only about each value: the first vertex of an inversely
rotated cone triangle is `Z⟦-1⟧` in `H⁰`, and by the object lemma below that
is the value of the dg shifted functor.

The equality and natural isomorphism are categorical interfaces.  The
sign-correct `CommShift` and exactness packages below transport through that
interface.  The direct `CommShift` package obtained from the shifted dg
functor is proved to agree with that transport, and the compatibility survives
ordinary endpoint equivalences; the two computation lemmas remain available
for strict objectwise formulas.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v vX vY u u' uX uY

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]
  [IsPretriangulated D]

/-- **On objects, the dg shifted functor is the `H⁰` shift.**  Both choose the
shifted object with `IsPretriangulated.exists_shift`, so this is `rfl`.

Not `@[simp]`: `h0_obj` and `shiftedFunctor_obj` both rewrite inside this
statement's own left-hand side, so it is not in simp normal form.  Use it with
`rw`. -/
theorem shiftedFunctor_h0_obj (F : DGFunctor C D) (n : ℤ) (X : H0 C) :
    (F.shiftedFunctor n).h0.obj X =
      (CategoryTheory.shiftFunctor (H0 D) n).obj (F.h0.obj X) :=
  rfl

/-- **On morphisms too.**  The Koszul sign is `+1` because an `H⁰` morphism has
degree zero, and the two transports agree by
`IsShiftBy.shiftMap_zero_eq_mapShift`. -/
@[simp]
theorem shiftedFunctor_h0_map (F : DGFunctor C D) (n : ℤ) {X Y : H0 C}
    (f : X ⟶ Y) :
    (F.shiftedFunctor n).h0.map f =
      (CategoryTheory.shiftFunctor (H0 D) n).map (F.h0.map f) := by
  induction f using Quotient.ind with
  | _ f =>
    refine congrArg (fun z => H0.homMk (C := D) z) (Subtype.ext ?_)
    show (n * 0).negOnePow •
        (F.shiftWitness n (H0.of C X)).shiftMap (F.shiftWitness n (H0.of C Y)) 0
          (F.map 0 (f : (dgHom (H0.of C X) (H0.of C Y)).X 0)) =
      IsShiftBy.mapShift (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) n)
        (IsPretriangulated.shiftWitness D (F.obj (H0.of C Y)) n)
        (F.map 0 (f : (dgHom (H0.of C X) (H0.of C Y)).X 0))
    rw [mul_zero, Int.negOnePow_zero, one_smul,
      IsShiftBy.shiftMap_zero_eq_mapShift]
    -- The two witnesses are the same choice: both are
    -- `(IsPretriangulated.exists_shift (F.obj X) n).choose_spec.some`.
    rfl

/-- The object and morphism computations assemble into an equality of ordinary
functors. -/
theorem shiftedFunctor_h0_eq (F : DGFunctor C D) (n : ℤ) :
    (F.shiftedFunctor n).h0 =
      F.h0 ⋙ CategoryTheory.shiftFunctor (H0 D) n := by
  exact Functor.hext (fun _ => rfl) (fun X Y f =>
    heq_of_eq (F.shiftedFunctor_h0_map n f))

/-- **The dg shift computes the pointwise shift on `H⁰`, functorially.**

This categorical interface packages `shiftedFunctor_h0_eq` as a natural
isomorphism for consumers that should transport structure through isomorphism
rather than rewrite functors. -/
noncomputable def shiftedFunctorH0Iso (F : DGFunctor C D) (n : ℤ) :
    (F.shiftedFunctor n).h0 ≅
      F.h0 ⋙ CategoryTheory.shiftFunctor (H0 D) n :=
  eqToIso (F.shiftedFunctor_h0_eq n)

/-- The comparison `H⁰(F[n]) ≅ H⁰(F)[n]` is the identity on each
object; only its functorial typing records the morphism computation. -/
@[simp]
theorem shiftedFunctorH0Iso_hom_app (F : DGFunctor C D) (n : ℤ) (X : H0 C) :
    (F.shiftedFunctorH0Iso n).hom.app X = 𝟙 _ := by
  rw [shiftedFunctorH0Iso, eqToIso.hom, eqToHom_app]
  have hp : Functor.congr_obj (F.shiftedFunctor_h0_eq n) X =
      F.shiftedFunctor_h0_obj n X := Subsingleton.elim _ _
  rw [hp]
  exact eqToHom_refl _ _

/-- The inverse comparison is likewise the identity on each object. -/
@[simp]
theorem shiftedFunctorH0Iso_inv_app (F : DGFunctor C D) (n : ℤ) (X : H0 C) :
    (F.shiftedFunctorH0Iso n).inv.app X = 𝟙 _ := by
  rw [shiftedFunctorH0Iso, eqToIso.inv, eqToHom_app]
  have hp : Functor.congr_obj (F.shiftedFunctor_h0_eq n).symm X =
      (F.shiftedFunctor_h0_obj n X).symm := Subsingleton.elim _ _
  rw [hp]
  exact eqToHom_refl _ _

section CommShift

variable [IsPretriangulated C]

set_option backward.isDefEq.respectTransparency false in
private lemma shiftedFunctor_h0CommShift_eq_ofIso
    (F : DGFunctor C D) (n : ℤ) :
    (F.shiftedFunctor n).h0CommShift = by
      letI : F.h0.CommShift ℤ := F.h0CommShift
      letI : (shiftFunctor (H0 D) n).CommShift ℤ :=
        Pretriangulated.shiftFunctorCommShift (H0 D) n
      letI : (F.h0 ⋙ shiftFunctor (H0 D) n).CommShift ℤ := inferInstance
      exact Functor.CommShift.ofIso (F.shiftedFunctorH0Iso n).symm ℤ := by
  letI : F.h0.CommShift ℤ := F.h0CommShift
  letI : (shiftFunctor (H0 D) n).CommShift ℤ :=
    Pretriangulated.shiftFunctorCommShift (H0 D) n
  letI : (F.h0 ⋙ shiftFunctor (H0 D) n).CommShift ℤ := inferInstance
  apply Functor.CommShift.ext
  intro a
  ext X
  simp only [Functor.CommShift.ofIso_commShiftIso_hom_app,
    Iso.symm_hom, Iso.symm_inv, shiftedFunctorH0Iso_hom_app,
    shiftedFunctorH0Iso_inv_app, Functor.map_id, Category.comp_id,
    Category.id_comp, Functor.commShiftIso_comp_hom_app,
    Pretriangulated.shiftFunctorCommShift_commShiftIso_hom_app]
  change (shiftCommIso (F.shiftedFunctor n)
      (preservesShifts (F.shiftedFunctor n)) a).hom.app X = _
  change H0.homMk (C := D) _ = _
  change H0.homMk (C := D) _ =
    (shiftFunctor (H0 D) n).map
        ((shiftCommIso F (preservesShifts F) a).hom.app X) ≫ _
  change H0.homMk (C := D) _ =
    (H0.shiftFunctor D n).map
        (H0.homMk (C := D) ⟨IsShiftBy.compare
          ((preservesShifts F).mapShift
            (IsPretriangulated.shiftWitness C (H0.of C X) a))
          (IsPretriangulated.shiftWitness D (F.obj (H0.of C X)) a), _⟩) ≫ _
  unfold H0.homMk
  rw [H0.shiftFunctor_map_mk]
  rw [H0.shiftFunctorComm_hom_app]
  change H0.homMk (C := D) _ = H0.homMk (C := D) _ ≫
    ((n * a).negOnePow • H0.homMk (C := D) _)
  rw [Units.smul_def, Preadditive.comp_zsmul, H0.homMk_comp]
  change H0.homMk (C := D) _ = H0.homMk (C := D) _
  let x := H0.of C X
  let sC := IsPretriangulated.shiftWitness C x a
  let A := (preservesShifts (F.shiftedFunctor n)).mapShift sC
  let B := IsPretriangulated.shiftWitness D ((F.shiftedFunctor n).obj x) a
  let p := (preservesShifts F).mapShift sC
  let q := IsPretriangulated.shiftWitness D (F.obj x) a
  let sn := F.shiftWitness n x
  let u := F.shiftWitness n (IsPretriangulated.shiftObj C x a)
  let v := IsPretriangulated.shiftWitness D
    (IsPretriangulated.shiftObj D (F.obj x) a) n
  refine congrArg _ (Subtype.ext ?_)
  change IsShiftBy.compare A B = (n * a).negOnePow •
    dgComp (C := D) 0 0 0 (by omega)
      (IsShiftBy.mapShift u v (IsShiftBy.compare p q))
      (IsShiftBy.compare (q.comp' v (a + n) rfl)
        (sn.comp' B (a + n) (by omega)))
  rw [IsShiftBy.mapShift_compare_comp', IsShiftBy.compare_trans]
  change IsShiftBy.compare A B = (n * a).negOnePow •
    IsShiftBy.compare (p.comp' u (a + n) rfl)
      (sn.comp' B (a + n) (by omega))
  have hA :
      (sn.comp' A (a + n) (by omega)).hom =
        (n * a).negOnePow • (p.comp' u (a + n) rfl).hom := by
    simp only [IsShiftBy.comp'_hom]
    rw [(preservesShifts (F.shiftedFunctor n)).mapShift_hom,
      F.shiftedFunctor_map]
    rw [dgComp_units_smul_right]
    rw [show n * -a = -(n * a) by ring, Int.negOnePow_neg]
    rw [← (preservesShifts F).mapShift_hom sC]
    apply congrArg (fun z => (n * a).negOnePow • z)
    exact sn.hom_comp_shiftMap u (-a) (-(a + n)) (by omega) (by omega) p.hom
  rw [← IsShiftBy.compare_compLeftOfDegree (m := a) (nm := a + n)
    sn A B (by omega)]
  apply IsShiftBy.compare_unique
  rw [hA, dgComp_units_smul_left, dgComp_units_smul_right,
    smul_smul, Int.units_mul_self, one_smul,
    IsShiftBy.hom_comp_compare]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison `H⁰(F[n]) ≅ H⁰(F)[n]` is compatible with
the direct shift package on `H⁰(F[n])`, the canonical package on `H⁰(F)`,
and the Koszul-signed package on `[n]`.

The source package is the one constructed directly from the shifted dg
functor, rather than a package manufactured by transporting across this
isomorphism. -/
theorem shiftedFunctorH0Iso_commShift (F : DGFunctor C D) (n : ℤ) :
    letI : (F.shiftedFunctor n).h0.CommShift ℤ :=
      (F.shiftedFunctor n).h0CommShift
    letI : F.h0.CommShift ℤ := F.h0CommShift
    letI : (shiftFunctor (H0 D) n).CommShift ℤ :=
      Pretriangulated.shiftFunctorCommShift (H0 D) n
    letI : (F.h0 ⋙ shiftFunctor (H0 D) n).CommShift ℤ := inferInstance
    NatTrans.CommShift (F.shiftedFunctorH0Iso n).hom ℤ := by
  letI : F.h0.CommShift ℤ := F.h0CommShift
  letI : (shiftFunctor (H0 D) n).CommShift ℤ :=
    Pretriangulated.shiftFunctorCommShift (H0 D) n
  letI : (F.h0 ⋙ shiftFunctor (H0 D) n).CommShift ℤ := inferInstance
  let e := (F.shiftedFunctorH0Iso n).symm
  rw [shiftedFunctor_h0CommShift_eq_ofIso F n]
  letI : (F.shiftedFunctor n).h0.CommShift ℤ :=
    Functor.CommShift.ofIso e ℤ
  haveI : NatTrans.CommShift e.hom ℤ :=
    Functor.CommShift.ofIso_compatibility e ℤ
  exact NatTrans.CommShift.of_iso_inv e ℤ

end CommShift

section Transport

variable {X : Type uX} {Y : Type uY}
  [Category.{vX} X] [Category.{vY} Y]

/-- Transporting `H⁰` of a shifted dg functor through ordinary equivalences
agrees with transporting `H⁰` first and then shifting in the target.

Only the forward target equivalence needs a shift comparison: the shift occurs
after `H⁰ F`, so no `CommShift` structure is required on the source
equivalence. -/
noncomputable def transportedShiftedFunctorH0Iso (F : DGFunctor C D) (n : ℤ)
    (eC : H0 C ≌ X) (eD : H0 D ≌ Y) [HasShift Y ℤ]
    [eD.functor.CommShift ℤ] :
    (eC.inverse ⋙ (F.shiftedFunctor n).h0) ⋙ eD.functor ≅
      ((eC.inverse ⋙ F.h0) ⋙ eD.functor) ⋙ shiftFunctor Y n :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft eC.inverse (F.shiftedFunctorH0Iso n))
      eD.functor ≪≫
    Functor.associator eC.inverse
      (F.h0 ⋙ shiftFunctor (H0 D) n) eD.functor ≪≫
    Functor.isoWhiskerLeft eC.inverse
      (Functor.associator F.h0 (shiftFunctor (H0 D) n) eD.functor) ≪≫
    (Functor.associator eC.inverse F.h0
      (shiftFunctor (H0 D) n ⋙ eD.functor)).symm ≪≫
    Functor.isoWhiskerLeft (eC.inverse ⋙ F.h0)
      (eD.functor.commShiftIso n) ≪≫
    (Functor.associator (eC.inverse ⋙ F.h0) eD.functor
      (shiftFunctor Y n)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The transported comparison `H⁰(F[n]) ≅ H⁰(F)[n]` respects the
canonical shift packages at both endpoints and the Koszul-signed package on
the final shift functor.

Additivity of the forward target equivalence is exactly what lets its shift
comparison commute with the Koszul sign. -/
theorem transportedShiftedFunctorH0Iso_commShift
    (F : DGFunctor C D) (n : ℤ) (eC : H0 C ≌ X) (eD : H0 D ≌ Y)
    [IsPretriangulated C]
    [HasShift X ℤ] [HasShift Y ℤ]
    [eC.functor.CommShift ℤ] [eD.functor.CommShift ℤ]
    [Preadditive Y] [∀ k : ℤ, (shiftFunctor Y k).Additive]
    [eD.functor.Additive] :
    letI : ((F.shiftedFunctor n).transportedH0 eC eD).CommShift ℤ :=
      (F.shiftedFunctor n).transportedH0CommShift
    letI : (F.transportedH0 eC eD).CommShift ℤ :=
      F.transportedH0CommShift
    letI : (shiftFunctor Y n).CommShift ℤ :=
      Pretriangulated.shiftFunctorCommShift Y n
    letI : (F.transportedH0 eC eD ⋙ shiftFunctor Y n).CommShift ℤ :=
      inferInstance
    NatTrans.CommShift (F.transportedShiftedFunctorH0Iso n eC eD).hom ℤ := by
  letI : eC.inverse.CommShift ℤ := eC.commShiftInverse ℤ
  letI : F.h0.CommShift ℤ := F.h0CommShift
  letI : (F.shiftedFunctor n).h0.CommShift ℤ :=
    (F.shiftedFunctor n).h0CommShift
  letI : (shiftFunctor (H0 D) n).CommShift ℤ :=
    Pretriangulated.shiftFunctorCommShift (H0 D) n
  letI : (shiftFunctor Y n).CommShift ℤ :=
    Pretriangulated.shiftFunctorCommShift Y n
  letI : (F.h0 ⋙ shiftFunctor (H0 D) n).CommShift ℤ := inferInstance
  haveI : NatTrans.CommShift (F.shiftedFunctorH0Iso n).hom ℤ :=
    F.shiftedFunctorH0Iso_commShift n
  haveI : NatTrans.CommShift (eD.functor.commShiftIso n).hom ℤ :=
    Pretriangulated.commShiftIso_commShift (H0 D) eD.functor n
  haveI : NatTrans.CommShift
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft eC.inverse (F.shiftedFunctorH0Iso n))
        eD.functor).hom ℤ := by
    change NatTrans.CommShift
      (Functor.whiskerRight
        (Functor.whiskerLeft eC.inverse (F.shiftedFunctorH0Iso n).hom)
        eD.functor) ℤ
    infer_instance
  haveI : NatTrans.CommShift
      (Functor.associator eC.inverse
        (F.h0 ⋙ shiftFunctor (H0 D) n) eD.functor).hom ℤ := by
    infer_instance
  haveI : NatTrans.CommShift
      (Functor.isoWhiskerLeft eC.inverse
        (Functor.associator F.h0 (shiftFunctor (H0 D) n) eD.functor)).hom ℤ := by
    change NatTrans.CommShift
      (Functor.whiskerLeft eC.inverse
        (Functor.associator F.h0 (shiftFunctor (H0 D) n) eD.functor).hom) ℤ
    infer_instance
  haveI : NatTrans.CommShift
      (Functor.associator eC.inverse F.h0
        (shiftFunctor (H0 D) n ⋙ eD.functor)).symm.hom ℤ := by
    infer_instance
  haveI : NatTrans.CommShift
      (Functor.isoWhiskerLeft (eC.inverse ⋙ F.h0)
        (eD.functor.commShiftIso n)).hom ℤ := by
    change NatTrans.CommShift
      (Functor.whiskerLeft (eC.inverse ⋙ F.h0)
        (eD.functor.commShiftIso n).hom) ℤ
    infer_instance
  haveI : NatTrans.CommShift
      (Functor.associator (eC.inverse ⋙ F.h0) eD.functor
        (shiftFunctor Y n)).symm.hom ℤ := by
    infer_instance
  change NatTrans.CommShift
    ((Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft eC.inverse (F.shiftedFunctorH0Iso n))
        eD.functor).hom ≫
      (Functor.associator eC.inverse
        (F.h0 ⋙ shiftFunctor (H0 D) n) eD.functor).hom ≫
      (Functor.isoWhiskerLeft eC.inverse
        (Functor.associator F.h0 (shiftFunctor (H0 D) n) eD.functor)).hom ≫
      (Functor.associator eC.inverse F.h0
        (shiftFunctor (H0 D) n ⋙ eD.functor)).symm.hom ≫
      (Functor.isoWhiskerLeft (eC.inverse ⋙ F.h0)
        (eD.functor.commShiftIso n)).hom ≫
      (Functor.associator (eC.inverse ⋙ F.h0) eD.functor
        (shiftFunctor Y n)).symm.hom) ℤ
  infer_instance

end Transport

/-- If `H⁰ F` is an equivalence, then so is `H⁰` of every shifted dg functor.

This is only an ordinary categorical conclusion; it neither asserts that the
shifted dg functor is a quasi-equivalence nor supplies triangulatedness. -/
theorem shiftedFunctor_h0_isEquivalence (F : DGFunctor C D) (n : ℤ)
    (hF : F.h0.IsEquivalence) : (F.shiftedFunctor n).h0.IsEquivalence := by
  letI := hF
  haveI : (F.h0 ⋙ CategoryTheory.shiftFunctor (H0 D) n).IsEquivalence :=
    inferInstance
  exact Functor.isEquivalence_of_iso (F.shiftedFunctorH0Iso n).symm

/-- The ordinary equivalence on `H⁰` induced from an equivalence `H⁰ F` after
shifting the dg functor. -/
noncomputable def shiftedFunctorH0Equivalence (F : DGFunctor C D) (n : ℤ)
    (hF : F.h0.IsEquivalence) : H0 C ≌ H0 D :=
  letI := F.shiftedFunctor_h0_isEquivalence n hF
  (F.shiftedFunctor n).h0.asEquivalence

section Exactness

variable {A : Type u} {B : Type u'} [DGCategory.{v} A] [DGCategory.{v} B]
  [IsPretriangulated A] [IsPretriangulated B]

set_option backward.isDefEq.respectTransparency false in
/-- The sign-correct shift comparison on `H⁰` of a shifted dg functor.

It is obtained by composing the canonical comparison on `H⁰(F)` with the
signed comparison on `[n]`, then transporting that structure across
`shiftedFunctorH0Iso`.  The result is explicit rather than a global instance,
so consumers control which shift comparison is in scope. -/
@[reducible]
noncomputable def shiftedFunctorH0CommShift (F : DGFunctor A B) (n : ℤ)
    (hF : PreservesShifts F) : (F.shiftedFunctor n).h0.CommShift ℤ := by
  letI : F.h0.CommShift ℤ :=
    commShift (C := A) (D := B) F hF
  letI : (shiftFunctor (H0 B) n).CommShift ℤ :=
    Pretriangulated.shiftFunctorCommShift (H0 B) n
  letI : (F.h0 ⋙ shiftFunctor (H0 B) n).CommShift ℤ := inferInstance
  exact Functor.CommShift.ofIso (F.shiftedFunctorH0Iso n).symm ℤ

set_option backward.isDefEq.respectTransparency false in
/-- A dg functor remains exact on `H⁰` after every integral dg shift.  The
shift argument selects the comparison used by `shiftedFunctorH0CommShift`;
cone preservation is automatic for every dg functor.

The proof composes the exact functor `H⁰(F)` with the sign-correct exact
ordinary shift `[n]`, then transports exactness across
`shiftedFunctorH0Iso`. -/
theorem shiftedFunctorH0IsTriangulated (F : DGFunctor A B) (n : ℤ)
    (hShift : PreservesShifts F) :
    letI : (F.shiftedFunctor n).h0.CommShift ℤ :=
      shiftedFunctorH0CommShift F n hShift
    (F.shiftedFunctor n).h0.IsTriangulated := by
  letI : F.h0.CommShift ℤ :=
    commShift (C := A) (D := B) F hShift
  letI : F.h0.IsTriangulated :=
    isTriangulated_of_preservesShifts_and_chosenCones
      (C := A) (D := B) F hShift (preservesChosenCones F)
  letI : (shiftFunctor (H0 B) n).CommShift ℤ :=
    Pretriangulated.shiftFunctorCommShift (H0 B) n
  letI : (shiftFunctor (H0 B) n).IsTriangulated :=
    Pretriangulated.shiftFunctorIsTriangulated (H0 B) n
  letI : (F.h0 ⋙ shiftFunctor (H0 B) n).CommShift ℤ := inferInstance
  letI : (F.h0 ⋙ shiftFunctor (H0 B) n).IsTriangulated := inferInstance
  let e := (F.shiftedFunctorH0Iso n).symm
  letI : (F.shiftedFunctor n).h0.CommShift ℤ :=
    shiftedFunctorH0CommShift F n hShift
  haveI : NatTrans.CommShift e.hom ℤ := by
    exact Functor.CommShift.ofIso_compatibility e ℤ
  exact Functor.isTriangulated_of_iso e

end Exactness

end DGFunctor

end CategoryTheory
