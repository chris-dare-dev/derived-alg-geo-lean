/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Functor

set_option backward.defeqAttrib.useBackward true

/-!
# Integral shifts as triangulated functors

The ordinary shift functor commutes with every shift, but for an odd shift the
commutation isomorphism used by a triangulated functor must carry the Koszul
sign.  This file packages that sign-correct comparison and proves that every
integral shift is triangulated with respect to it.

The structures are explicit definitions rather than global instances.  This
avoids an instance diamond with the unsigned comparison, which remains useful
for even shifts and object-only arguments.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C ℤ]

/-- The Koszul-signed comparison between shifting by `a` and then by `n`, and
shifting by `n` and then by `a`. -/
noncomputable def signedShiftFunctorCommIso (n a : ℤ) :
    shiftFunctor C a ⋙ shiftFunctor C n ≅ shiftFunctor C n ⋙ shiftFunctor C a :=
  (n * a).negOnePow • shiftFunctorComm C a n

set_option backward.isDefEq.respectTransparency false in
omit [Preadditive C] in
private theorem shiftFunctorComm_add (n a b : ℤ) :
    shiftFunctorComm C (a + b) n =
      Functor.CommShift.isoAdd (shiftFunctorComm C a n) (shiftFunctorComm C b n) := by
  rw [← shiftFunctorComm_symm]
  ext X
  simp only [Iso.symm_hom, Functor.CommShift.isoAdd_hom_app]
  rw [← cancel_epi ((shiftFunctorComm C n (a + b)).hom.app X)]
  simp only [Iso.hom_inv_id_app]
  rw [shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app_assoc]
  rw [show shiftFunctorComm C b n = (shiftFunctorComm C n b).symm by
    rw [shiftFunctorComm_symm]]
  rw [show shiftFunctorComm C a n = (shiftFunctorComm C n a).symm by
    rw [shiftFunctorComm_symm]]
  simp only [Iso.symm_hom, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [(shiftFunctor C b).map_id, Category.id_comp, Iso.hom_inv_id_app]

set_option backward.isDefEq.respectTransparency false in
/-- The unsigned `CommShift` structure on an integral shift functor.

For odd `n` this is not the structure that makes the shift functor
triangulated.  It is retained as explicit data for sign-free and object-only
arguments. -/
@[implicit_reducible]
noncomputable def shiftFunctorUnsignedCommShift (n : ℤ) :
    (shiftFunctor C n).CommShift ℤ where
  commShiftIso a := shiftFunctorComm C a n
  commShiftIso_zero := by
    change shiftFunctorComm C 0 n = _
    rw [← shiftFunctorComm_symm]
    ext X
    simp only [Iso.symm_hom, Functor.CommShift.isoZero_hom_app]
    rw [← cancel_epi ((shiftFunctorComm C n 0).hom.app X)]
    rw [Iso.hom_inv_id_app]
    symm
    rw [← Category.assoc, ← shiftFunctorZero_hom_app_shift]
    simp
  commShiftIso_add a b := shiftFunctorComm_add C n a b

variable [∀ n : ℤ, (shiftFunctor C n).Additive]

set_option backward.isDefEq.respectTransparency false in
/-- The sign-correct `CommShift` structure on an integral shift functor. -/
@[implicit_reducible]
noncomputable def shiftFunctorCommShift (n : ℤ) :
    (shiftFunctor C n).CommShift ℤ where
  commShiftIso a := signedShiftFunctorCommIso C n a
  commShiftIso_zero := by
    change (n * 0).negOnePow • shiftFunctorComm C 0 n = _
    rw [mul_zero, Int.negOnePow_zero]
    rw [← shiftFunctorComm_symm]
    ext X
    dsimp
    simp only [one_smul, Functor.CommShift.isoZero_hom_app]
    rw [← cancel_epi ((shiftFunctorComm C n 0).hom.app X)]
    rw [Iso.hom_inv_id_app]
    symm
    rw [← Category.assoc, ← shiftFunctorZero_hom_app_shift]
    simp
  commShiftIso_add a b := by
    ext X
    dsimp [signedShiftFunctorCommIso]
    simp only [Functor.CommShift.isoAdd_hom_app]
    change (n * (a + b)).negOnePow • (shiftFunctorComm C (a + b) n).hom.app X =
      (shiftFunctor C n).map ((shiftFunctorAdd C a b).hom.app X) ≫
        ((n * b).negOnePow •
          (shiftFunctorComm C b n).hom.app ((shiftFunctor C a).obj X)) ≫
          (shiftFunctor C b).map
            ((n * a).negOnePow • (shiftFunctorComm C a n).hom.app X) ≫
            (shiftFunctorAdd C a b).inv.app ((shiftFunctor C n).obj X)
    have h := NatTrans.congr_app
      (congr_arg Iso.hom (shiftFunctorComm_add C n a b)) X
    simpa only [mul_add, Int.negOnePow_add,
      Functor.CommShift.isoAdd_hom_app, Functor.map_units_smul, Linear.units_smul_comp,
      Linear.comp_units_smul, smul_smul] using
        congr_arg (fun f :
            (shiftFunctor C (a + b) ⋙ shiftFunctor C n).obj X ⟶
              (shiftFunctor C n ⋙ shiftFunctor C (a + b)).obj X =>
          ((n * a).negOnePow * (n * b).negOnePow) • f) h

@[simp]
lemma shiftFunctorCommShift_commShiftIso_hom_app (n a : ℤ) (X : C) :
    letI := shiftFunctorCommShift C n
    ((shiftFunctor C n).commShiftIso a).hom.app X =
      (n * a).negOnePow • (shiftFunctorComm C a n).hom.app X := by
  rfl

variable [HasZeroObject C] [Pretriangulated C]

/-- The parity-sign automorphism used at the middle vertex of a shifted
triangle. -/
noncomputable def shiftSignIso (n : ℤ) (X : C) : X ≅ X where
  hom := n.negOnePow • 𝟙 X
  inv := n.negOnePow • 𝟙 X
  hom_inv_id := by
    simp only [Linear.comp_units_smul, Category.comp_id, smul_smul,
      Int.units_mul_self, one_smul]
  inv_hom_id := by
    simp only [Linear.comp_units_smul, Category.comp_id, smul_smul,
      Int.units_mul_self, one_smul]

/-- Mapping a triangle by `[n]` with the sign-correct `CommShift` agrees with
the canonical shift of that triangle. -/
noncomputable def shiftFunctorMapTriangleIso (n : ℤ) :
    letI := shiftFunctorCommShift C n
    (shiftFunctor C n).mapTriangle ≅ Triangle.shiftFunctor C n := by
  letI := shiftFunctorCommShift C n
  exact NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _)
      (shiftSignIso C n _) (Iso.refl _)
      (by
        dsimp [shiftFunctorCommShift, signedShiftFunctorCommIso, shiftSignIso]
        simp only [Linear.comp_units_smul, Category.comp_id, Category.id_comp])
      (by
        dsimp [shiftFunctorCommShift, signedShiftFunctorCommIso, shiftSignIso]
        simp only [Category.comp_id, Linear.units_smul_comp, Linear.comp_units_smul,
          smul_smul, Int.units_mul_self, one_smul, Category.id_comp])
      (by
        dsimp [shiftFunctorCommShift, signedShiftFunctorCommIso]
        simp only [Functor.map_id, Category.comp_id, Category.id_comp]
        rw [shiftFunctorCommShift_commShiftIso_hom_app]
        rw [mul_one]
        exact Linear.comp_units_smul _ _ _))
    (by
      intro X Y f
      ext <;> dsimp [shiftSignIso] <;> simp)

/-- Every integral shift is triangulated when equipped with the sign-correct
`CommShift` structure. -/
theorem shiftFunctorIsTriangulated (n : ℤ) :
    letI := shiftFunctorCommShift C n
    (shiftFunctor C n).IsTriangulated := by
  letI := shiftFunctorCommShift C n
  exact
    { map_distinguished := fun T hT =>
        isomorphic_distinguished _ (Triangle.shift_distinguished T hT n) _
          ((shiftFunctorMapTriangleIso C n).app T) }

set_option backward.isDefEq.respectTransparency false in
/-- For an even `n`, the unsigned comparison also identifies triangle mapping
by `[n]` with the canonical triangle shift. -/
noncomputable def shiftFunctorUnsignedMapTriangleIso (n : ℤ) (hn : Even n) :
    letI := shiftFunctorUnsignedCommShift C n
    (shiftFunctor C n).mapTriangle ≅ Triangle.shiftFunctor C n := by
  letI := shiftFunctorUnsignedCommShift C n
  exact NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by dsimp; rw [Int.negOnePow_even n hn]; simp)
      (by dsimp; rw [Int.negOnePow_even n hn]; simp)
      (by
        dsimp
        rw [(shiftFunctor C 1).map_id, Category.comp_id, Category.id_comp]
        change (shiftFunctor C n).map T.mor₃ ≫
          (shiftFunctorComm C 1 n).hom.app T.obj₁ = _
        rw [Int.negOnePow_even n hn]
        simp))
    (by cat_disch)

/-- An even integral shift is triangulated with the unsigned `CommShift`
presentation.  This is a compatibility interface; the signed presentation
works uniformly for every integer. -/
theorem shiftFunctorUnsignedIsTriangulated (n : ℤ) (hn : Even n) :
    letI := shiftFunctorUnsignedCommShift C n
    (shiftFunctor C n).IsTriangulated := by
  letI := shiftFunctorUnsignedCommShift C n
  exact
    { map_distinguished := fun T hT =>
        isomorphic_distinguished _ (Triangle.shift_distinguished T hT n) _
          ((shiftFunctorUnsignedMapTriangleIso C n hn).app T) }

end CategoryTheory.Pretriangulated
