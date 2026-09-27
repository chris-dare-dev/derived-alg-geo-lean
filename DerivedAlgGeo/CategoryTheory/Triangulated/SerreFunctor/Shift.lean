/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Linear.SerreFunctor.Conjugation
import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Serre functors and shifts

The shift comparison comes from conjugation by the shift equivalence and
uniqueness of the Serre functor. Applying Serre uniqueness directly to
`S ⋙ [1]` and `[1] ⋙ S` is invalid: either functor represents the dual of
`Hom(A, B⟦-1⟧)`, rather than the dual of `Hom(A, B)`.

The displayed comparison is coherent in the shift index. The resulting
`CommShift ℤ` does not itself establish preservation of distinguished triangles;
that separate exactness argument must use the signed rotation convention.

## Main definition

`SerreFunctorData.commShiftIso n` specializes linear conjugation transport to
the equivalence given by the single shift `n`. `SerreFunctorData.commShift`
assembles these comparisons into a coherent `CommShift ℤ` structure.
-/

universe w v u

namespace CategoryTheory.SerreFunctor.SerreFunctorData

open CategoryTheory

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [HasShift C ℤ]

/-- The Serre functor commutes with each shift, by conjugation with the
corresponding shift equivalence. This is the orientation used in #898;
Mathlib's `CommShift` stores the inverse orientation. -/
noncomputable def commShiftIso (D : SerreFunctorData k C) (n : ℤ)
    [(shiftFunctor C n).Additive] [(shiftFunctor C n).Linear k] :
    D.S ⋙ shiftFunctor C n ≅ shiftFunctor C n ⋙ D.S := by
  letI : (shiftEquiv C n).functor.Additive := by
    change (shiftFunctor C n).Additive
    infer_instance
  letI : (shiftEquiv C n).functor.Linear k := by
    change (shiftFunctor C n).Linear k
    infer_instance
  exact (D.transportIso (shiftEquiv C n)).symm

section CoherentShift

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (D : SerreFunctorData k C)

private local instance reflAdditive :
    (CategoryTheory.Equivalence.refl : C ≌ C).functor.Additive := by
  change (𝟭 C).Additive
  infer_instance

private local instance reflLinear :
    (CategoryTheory.Equivalence.refl : C ≌ C).functor.Linear k := by
  change (𝟭 C).Linear k
  infer_instance

private local instance shiftAdditive
    [∀ n : ℤ, (shiftFunctor C n).Additive] (n : ℤ) :
    (shiftEquiv C n).functor.Additive := by
  change (shiftFunctor C n).Additive
  infer_instance

private local instance shiftLinear
    [∀ n : ℤ, (shiftFunctor C n).Linear k] (n : ℤ) :
    (shiftEquiv C n).functor.Linear k := by
  change (shiftFunctor C n).Linear k
  infer_instance

omit [HasShift C ℤ] in
private theorem transportIso_refl_inv_app (A : C) :
    (D.transportIso (CategoryTheory.Equivalence.refl : C ≌ C)).inv.app A = 𝟙 _ := by
  rw [D.transportIso_refl]
  simp

private theorem transportIso_shift_zero_inv_app
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear k]
    (A : C) :
    (D.transportIso (shiftEquiv C (0 : ℤ))).inv.app A =
      (Functor.CommShift.isoZero D.S ℤ).inv.app A := by
  let T : C ≌ C := shiftEquiv C (0 : ℤ)
  let R : C ≌ C := CategoryTheory.Equivalence.refl
  letI : T.functor.Additive := by
    change (shiftFunctor C (0 : ℤ)).Additive
    infer_instance
  letI : T.functor.Linear k := by
    change (shiftFunctor C (0 : ℤ)).Linear k
    infer_instance
  letI : R.functor.Additive := by
    change (𝟭 C).Additive
    infer_instance
  letI : R.functor.Linear k := by
    change (𝟭 C).Linear k
    infer_instance
  let e : T.functor ≅ R.functor := shiftFunctorZero C ℤ
  have h := transportIso_isoCompat D T R e A
  change (shiftFunctorZero C ℤ).hom.app (D.S.obj A) ≫
      (D.transportIso (CategoryTheory.Equivalence.refl : C ≌ C)).inv.app A =
    (D.transportIso (shiftEquiv C (0 : ℤ))).inv.app A ≫
      D.S.map ((shiftFunctorZero C ℤ).hom.app A) at h
  rw [transportIso_refl_inv_app D A] at h
  erw [Category.comp_id] at h
  rw [Functor.CommShift.isoZero_inv_app]
  calc
    (D.transportIso (shiftEquiv C (0 : ℤ))).inv.app A =
      ((D.transportIso (shiftEquiv C (0 : ℤ))).inv.app A ≫
        D.S.map ((shiftFunctorZero C ℤ).hom.app A)) ≫
        D.S.map ((shiftFunctorZero C ℤ).inv.app A) := by
          erw [Category.assoc, ← D.S.map_comp, Iso.hom_inv_id_app, D.S.map_id, Category.comp_id]
    _ = (shiftFunctorZero C ℤ).hom.app (D.S.obj A) ≫
      D.S.map ((shiftFunctorZero C ℤ).inv.app A) := by rw [← h]

private theorem transportIso_shift_add_inv_app
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear k]
    (n m : ℤ) (A : C) :
    (D.transportIso (shiftEquiv C (n + m))).inv.app A =
      (Functor.CommShift.isoAdd
        (D.transportIso (shiftEquiv C n))
        (D.transportIso (shiftEquiv C m))).inv.app A := by
  let Tn : C ≌ C := shiftEquiv C n
  let Tm : C ≌ C := shiftEquiv C m
  let P : C ≌ C := shiftEquiv C (n + m)
  let Q : C ≌ C := Tn.trans Tm
  letI : Q.functor.Additive := by
    change (shiftFunctor C n ⋙ shiftFunctor C m).Additive
    infer_instance
  letI : Q.functor.Linear k := by
    change (shiftFunctor C n ⋙ shiftFunctor C m).Linear k
    infer_instance
  let e : P.functor ≅ Q.functor := shiftFunctorAdd C n m
  have h := transportIso_isoCompat D P Q e A
  have ht := transportIso_trans D Tn Tm A
  change (shiftFunctorAdd C n m).hom.app (D.S.obj A) ≫
      (D.transportIso Q).inv.app A =
    (D.transportIso P).inv.app A ≫
      D.S.map ((shiftFunctorAdd C n m).hom.app A) at h
  rw [Functor.CommShift.isoAdd_inv_app]
  calc
    (D.transportIso P).inv.app A =
      ((D.transportIso P).inv.app A ≫
        D.S.map ((shiftFunctorAdd C n m).hom.app A)) ≫
        D.S.map ((shiftFunctorAdd C n m).inv.app A) := by
          erw [Category.assoc, ← D.S.map_comp, Iso.hom_inv_id_app,
            D.S.map_id, Category.comp_id]
    _ = ((shiftFunctorAdd C n m).hom.app (D.S.obj A) ≫
        (D.transportIso Q).inv.app A) ≫
        D.S.map ((shiftFunctorAdd C n m).inv.app A) := by rw [← h]
    _ = ((shiftFunctorAdd C n m).hom.app (D.S.obj A) ≫
        (Tm.functor.map ((D.transportIso Tn).inv.app A) ≫
          (D.transportIso Tm).inv.app (Tn.functor.obj A))) ≫
        D.S.map ((shiftFunctorAdd C n m).inv.app A) := by rw [ht]
    _ = (shiftFunctorAdd C n m).hom.app (D.S.obj A) ≫
        (shiftFunctor C m).map ((D.transportIso (shiftEquiv C n)).inv.app A) ≫
        (D.transportIso (shiftEquiv C m)).inv.app ((shiftFunctor C n).obj A) ≫
        D.S.map ((shiftFunctorAdd C n m).inv.app A) := by
          simp only [Category.assoc]
          rfl

/-- The conjugation transports give `D.S` a coherent commutation with integer
shifts. Its component at `n` is `(D.commShiftIso n).symm`; the zero and addition
laws follow from transport functoriality. Triangle preservation requires a
separate signed comparison. -/
@[implicit_reducible]
noncomputable def commShift
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear k] : D.S.CommShift ℤ where
  commShiftIso n := D.transportIso (shiftEquiv C n)
  commShiftIso_zero := by
    have hs : (D.transportIso (shiftEquiv C (0 : ℤ))).symm =
        (Functor.CommShift.isoZero D.S ℤ).symm := by
      apply Iso.ext
      ext A
      exact transportIso_shift_zero_inv_app D A
    simpa using congrArg Iso.symm hs
  commShiftIso_add n m := by
    have hs : (D.transportIso (shiftEquiv C (n + m))).symm =
        (Functor.CommShift.isoAdd
          (D.transportIso (shiftEquiv C n))
          (D.transportIso (shiftEquiv C m))).symm := by
      apply Iso.ext
      ext A
      exact transportIso_shift_add_inv_app D n m A
    simpa using congrArg Iso.symm hs

end CoherentShift

end CategoryTheory.SerreFunctor.SerreFunctorData
