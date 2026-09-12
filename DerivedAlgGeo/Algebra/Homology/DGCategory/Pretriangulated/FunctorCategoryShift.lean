/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Shift.Basic
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.FunctorCategory

/-!
# The shift on the closed category of dg functors

For pretriangulated `D`, `DGFunctor.shiftedFunctor` shifts a dg functor
`F : C ⟶ D` by an integer. The comparison transformations already say that
shifting by zero changes nothing and that shifting by `n` and then by `m`
agrees with shifting by `n + m`. This file packages exactly that data as

`HasShift (Z0 (DGFunctor C D)) ℤ`.

`Z0` is the right categorical boundary. The raw type `DGFunctor C D` is
enriched over complexes and has no ordinary category structure; in `Z0`, its
morphisms are the closed degree-zero homogeneous natural transformations, and
all four comparison transformations are therefore honest categorical
morphisms. No second shift abstraction is introduced: the package is
Mathlib's `ShiftMkCore`, hence its associativity and unit laws are the standard
ones consumed by `shiftFunctorAdd` and `shiftFunctorZero`.

## Direction of the additive comparison

`DGFunctor.shiftedFunctorAdd` points from the iterated shift to the total
shift. Mathlib's `ShiftMkCore.add` points the other way, from the total shift
to the iterated shift, so its `hom` is `shiftedFunctorAddInv` and its `inv` is
`shiftedFunctorAdd`. The associativity field is not reproved pointwise: the
two candidate `hom`s are identified because their inverse paths are precisely
`shiftedFunctorAddAssocLeft` and `shiftedFunctorAddAssocRight`, whose equality
is `shiftedFunctorAdd_assoc`.

The two unit fields are the remaining content. On the right they reduce to
the inverse of the zero comparison on `F[n]`; on the left they are the shift
of the inverse zero comparison on `F`. Both are consequences of the existing
`IsShiftBy` comparison calculus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]
  [IsPretriangulated D]

/-- Shift closed degree-zero transformations pointwise. Closedness is exactly
what makes the result a morphism of `Z0 (DGFunctor C D)`. -/
noncomputable def z0ShiftFunctor (n : ℤ) :
    Z0 (DGFunctor C D) ⥤ Z0 (DGFunctor C D) where
  obj F := (Z0.of (DGFunctor C D) F).shiftedFunctor n
  map α :=
    ⟨HomogeneousNatTrans.shiftedDegreeZero α.1 n,
      (HomogeneousNatTrans.complex_d_apply _).trans
        (HomogeneousNatTrans.shiftedDegreeZero_isClosed
          ((HomogeneousNatTrans.complex_d_apply α.1).symm.trans α.2) n)⟩
  map_id F := Subtype.ext (HomogeneousNatTrans.shiftedDegreeZero_id
    (Z0.of (DGFunctor C D) F) n)
  map_comp α β := Subtype.ext (HomogeneousNatTrans.shiftedDegreeZero_comp α.1 β.1 n)

@[simp]
lemma z0ShiftFunctor_obj (n : ℤ) (F : Z0 (DGFunctor C D)) :
    (z0ShiftFunctor (C := C) (D := D) n).obj F =
      (Z0.of (DGFunctor C D) F).shiftedFunctor n :=
  rfl

/-- The underlying transformation of the shifted `Z0` morphism. -/
lemma z0ShiftFunctor_map_val (n : ℤ) {F G : Z0 (DGFunctor C D)} (α : F ⟶ G) :
    ((z0ShiftFunctor (C := C) (D := D) n).map α).1 =
      HomogeneousNatTrans.shiftedDegreeZero α.1 n :=
  rfl

/-- The zero-shift comparison as a natural isomorphism of closed dg functors. -/
noncomputable def z0ShiftFunctorZeroIso :
    z0ShiftFunctor (C := C) (D := D) 0 ≅ 𝟭 (Z0 (DGFunctor C D)) :=
  NatIso.ofComponents
    (fun F =>
      { hom := ⟨(Z0.of (DGFunctor C D) F).shiftedFunctorZero,
          (HomogeneousNatTrans.complex_d_apply _).trans
            (Z0.of (DGFunctor C D) F).shiftedFunctorZero_isClosed⟩
        inv := ⟨(Z0.of (DGFunctor C D) F).shiftedFunctorZeroInv,
          (HomogeneousNatTrans.complex_d_apply _).trans
            (Z0.of (DGFunctor C D) F).shiftedFunctorZeroInv_isClosed⟩
        hom_inv_id := Subtype.ext
          (Z0.of (DGFunctor C D) F).shiftedFunctorZero_comp_inv
        inv_hom_id := Subtype.ext
          (Z0.of (DGFunctor C D) F).shiftedFunctorZeroInv_comp })
    (by
      intro F G α
      apply Subtype.ext
      change HomogeneousNatTrans.composition _ _ _ 0 0 0 (by omega)
          (HomogeneousNatTrans.shiftedDegreeZero α.1 0)
          (Z0.of (DGFunctor C D) G).shiftedFunctorZero =
        HomogeneousNatTrans.composition _ _ _ 0 0 0 (by omega)
          (Z0.of (DGFunctor C D) F).shiftedFunctorZero α.1
      apply HomogeneousNatTrans.ext
      intro X
      rw [HomogeneousNatTrans.composition_apply_app,
        HomogeneousNatTrans.composition_apply_app,
        HomogeneousNatTrans.shiftedDegreeZero_app,
        shiftedFunctorZero_app, shiftedFunctorZero_app]
      exact (IsShiftBy.shiftMap_compare
        ((Z0.of (DGFunctor C D) F).shiftWitness 0 X)
        (IsShiftBy.self ((Z0.of (DGFunctor C D) F).obj X))
        ((Z0.of (DGFunctor C D) G).shiftWitness 0 X)
        (IsShiftBy.self ((Z0.of (DGFunctor C D) G).obj X)) 0
        (HomogeneousNatTrans.app α.1 X)).trans
          (congrArg (fun z => dgComp 0 0 0 (by omega)
            (IsShiftBy.compare
              ((Z0.of (DGFunctor C D) F).shiftWitness 0 X)
              (IsShiftBy.self ((Z0.of (DGFunctor C D) F).obj X))) z)
            (IsShiftBy.shiftMap_self 0 (HomogeneousNatTrans.app α.1 X))))

@[simp]
lemma z0ShiftFunctorZeroIso_hom_app_val (F : Z0 (DGFunctor C D)) :
    ((z0ShiftFunctorZeroIso (C := C) (D := D)).hom.app F).1 =
      (Z0.of (DGFunctor C D) F).shiftedFunctorZero :=
  rfl

@[simp]
lemma z0ShiftFunctorZeroIso_inv_app_val (F : Z0 (DGFunctor C D)) :
    ((z0ShiftFunctorZeroIso (C := C) (D := D)).inv.app F).1 =
      (Z0.of (DGFunctor C D) F).shiftedFunctorZeroInv :=
  rfl

/-- The additive comparison as a natural isomorphism, with a free total
degree. The direction is Mathlib's: total shift to iterated shift. -/
noncomputable def z0ShiftFunctorAddIso' (n m nm : ℤ) (hnm : n + m = nm) :
    z0ShiftFunctor (C := C) (D := D) nm ≅
      z0ShiftFunctor n ⋙ z0ShiftFunctor m :=
  NatIso.ofComponents
    (fun F =>
      { hom := ⟨(Z0.of (DGFunctor C D) F).shiftedFunctorAddInv n m nm hnm,
          (HomogeneousNatTrans.complex_d_apply _).trans
            ((Z0.of (DGFunctor C D) F).shiftedFunctorAddInv_isClosed n m nm hnm)⟩
        inv := ⟨(Z0.of (DGFunctor C D) F).shiftedFunctorAdd n m nm hnm,
          (HomogeneousNatTrans.complex_d_apply _).trans
            ((Z0.of (DGFunctor C D) F).shiftedFunctorAdd_isClosed n m nm hnm)⟩
        hom_inv_id := Subtype.ext
          ((Z0.of (DGFunctor C D) F).shiftedFunctorAddInv_comp n m nm hnm)
        inv_hom_id := Subtype.ext
          ((Z0.of (DGFunctor C D) F).shiftedFunctorAdd_comp_inv n m nm hnm) })
    (by
      intro F G α
      apply Subtype.ext
      change HomogeneousNatTrans.composition _ _ _ 0 0 0 (by omega)
          (HomogeneousNatTrans.shiftedDegreeZero α.1 nm)
          ((Z0.of (DGFunctor C D) G).shiftedFunctorAddInv n m nm hnm) =
        HomogeneousNatTrans.composition _ _ _ 0 0 0 (by omega)
          ((Z0.of (DGFunctor C D) F).shiftedFunctorAddInv n m nm hnm)
          (HomogeneousNatTrans.shiftedDegreeZero
            (HomogeneousNatTrans.shiftedDegreeZero α.1 n) m)
      apply HomogeneousNatTrans.ext
      intro X
      let sF := (Z0.of (DGFunctor C D) F).shiftWitness n X
      let uF := ((Z0.of (DGFunctor C D) F).shiftedFunctor n).shiftWitness m X
      let sG := (Z0.of (DGFunctor C D) G).shiftWitness n X
      let uG := ((Z0.of (DGFunctor C D) G).shiftedFunctor n).shiftWitness m X
      let tF := (Z0.of (DGFunctor C D) F).shiftWitness nm X
      let tG := (Z0.of (DGFunctor C D) G).shiftWitness nm X
      rw [HomogeneousNatTrans.composition_apply_app,
        HomogeneousNatTrans.composition_apply_app,
        HomogeneousNatTrans.shiftedDegreeZero_app,
        HomogeneousNatTrans.shiftedDegreeZero_app,
        HomogeneousNatTrans.shiftedDegreeZero_app,
        shiftedFunctorAddInv_app, shiftedFunctorAddInv_app]
      change dgComp 0 0 0 (by omega)
          (tF.shiftMap tG 0 (HomogeneousNatTrans.app α.1 X))
          (IsShiftBy.compare tG (sG.comp' uG nm hnm)) =
        dgComp 0 0 0 (by omega)
          (IsShiftBy.compare tF (sF.comp' uF nm hnm))
          (uF.shiftMap uG 0
            (sF.shiftMap sG 0 (HomogeneousNatTrans.app α.1 X)))
      refine (IsShiftBy.shiftMap_compare tF (sF.comp' uF nm hnm)
        tG (sG.comp' uG nm hnm) 0
          (HomogeneousNatTrans.app α.1 X)).trans ?_
      exact congrArg (fun z => dgComp 0 0 0 (by omega)
        (IsShiftBy.compare tF (sF.comp' uF nm hnm)) z)
          (IsShiftBy.comp'_shiftMap sF uF sG uG nm hnm 0
            (HomogeneousNatTrans.app α.1 X)))

@[simp]
lemma z0ShiftFunctorAddIso'_hom_app_val (n m nm : ℤ) (hnm : n + m = nm)
    (F : Z0 (DGFunctor C D)) :
    ((z0ShiftFunctorAddIso' (C := C) (D := D) n m nm hnm).hom.app F).1 =
      (Z0.of (DGFunctor C D) F).shiftedFunctorAddInv n m nm hnm :=
  rfl

@[simp]
lemma z0ShiftFunctorAddIso'_inv_app_val (n m nm : ℤ) (hnm : n + m = nm)
    (F : Z0 (DGFunctor C D)) :
    ((z0ShiftFunctorAddIso' (C := C) (D := D) n m nm hnm).inv.app F).1 =
      (Z0.of (DGFunctor C D) F).shiftedFunctorAdd n m nm hnm :=
  rfl

/-- The additive comparison at the definitional total degree. -/
noncomputable def z0ShiftFunctorAddIso (n m : ℤ) :
    z0ShiftFunctor (C := C) (D := D) (n + m) ≅
      z0ShiftFunctor n ⋙ z0ShiftFunctor m :=
  z0ShiftFunctorAddIso' n m (n + m) rfl

/-- The right unit law for the additive comparison, in free-degree form. -/
lemma z0ShiftFunctorAddIso'_hom_app_zero_right (n nm : ℤ)
    (hnm : n + 0 = nm) (F : Z0 (DGFunctor C D)) :
    (z0ShiftFunctorAddIso' (C := C) (D := D) n 0 nm hnm).hom.app F =
      eqToHom (congrArg (fun k => (z0ShiftFunctor (C := C) (D := D) k).obj F)
        (show nm = n by omega)) ≫
        (z0ShiftFunctorZeroIso (C := C) (D := D)).inv.app
          ((z0ShiftFunctor n).obj F) := by
  obtain rfl : nm = n := by omega
  rw [eqToHom_refl, Category.id_comp]
  apply Subtype.ext
  change (Z0.of (DGFunctor C D) F).shiftedFunctorAddInv nm 0 nm hnm =
    ((Z0.of (DGFunctor C D) F).shiftedFunctor nm).shiftedFunctorZeroInv
  apply HomogeneousNatTrans.ext
  intro X
  change IsShiftBy.compare
      ((Z0.of (DGFunctor C D) F).shiftWitness nm X)
      (((Z0.of (DGFunctor C D) F).shiftWitness nm X).comp'
        (((Z0.of (DGFunctor C D) F).shiftedFunctor nm).shiftWitness 0 X) nm hnm) =
    IsShiftBy.compare
      (IsShiftBy.self (((Z0.of (DGFunctor C D) F).shiftedFunctor nm).obj X))
      (((Z0.of (DGFunctor C D) F).shiftedFunctor nm).shiftWitness 0 X)
  rw [IsShiftBy.compare, IsShiftBy.compare, IsShiftBy.comp'_hom,
    IsShiftBy.self_inv,
    ← dgComp_assoc nm (-nm) (-0) 0 (-nm) 0 (by omega) (by omega) (by omega),
    IsShiftBy.inv_hom]
  rfl

/-- The left unit law for the additive comparison, in free-degree form. -/
lemma z0ShiftFunctorAddIso'_hom_app_zero_left (n nm : ℤ)
    (hnm : 0 + n = nm) (F : Z0 (DGFunctor C D)) :
    (z0ShiftFunctorAddIso' (C := C) (D := D) 0 n nm hnm).hom.app F =
      eqToHom (congrArg (fun k => (z0ShiftFunctor (C := C) (D := D) k).obj F)
        (show nm = n by omega)) ≫
        (z0ShiftFunctor (C := C) (D := D) n).map
          ((z0ShiftFunctorZeroIso (C := C) (D := D)).inv.app F) := by
  obtain rfl : nm = n := by omega
  rw [eqToHom_refl, Category.id_comp]
  apply Subtype.ext
  change (Z0.of (DGFunctor C D) F).shiftedFunctorAddInv 0 nm nm hnm =
    HomogeneousNatTrans.shiftedDegreeZero
      (Z0.of (DGFunctor C D) F).shiftedFunctorZeroInv nm
  apply HomogeneousNatTrans.ext
  intro X
  let s := (Z0.of (DGFunctor C D) F).shiftWitness nm X
  let t := (Z0.of (DGFunctor C D) F).shiftWitness 0 X
  let u := ((Z0.of (DGFunctor C D) F).shiftedFunctor 0).shiftWitness nm X
  let st := (Z0.of (DGFunctor C D) F).shiftWitnessComp 0 nm nm hnm X
  let ss := (IsShiftBy.self ((Z0.of (DGFunctor C D) F).obj X)).comp' s nm hnm
  change IsShiftBy.compare s st =
    s.shiftMap u 0
      (IsShiftBy.compare (IsShiftBy.self ((Z0.of (DGFunctor C D) F).obj X)) t)
  have hmap := IsShiftBy.shiftMap_compare_compOfDegree (nm := nm)
    (IsShiftBy.self ((Z0.of (DGFunctor C D) F).obj X)) t s u hnm
  change s.shiftMap u 0
      (IsShiftBy.compare (IsShiftBy.self ((Z0.of (DGFunctor C D) F).obj X)) t) =
    IsShiftBy.compare ss st at hmap
  calc
    IsShiftBy.compare s st = IsShiftBy.compare ss st := by
      rw [IsShiftBy.compare, IsShiftBy.compare,
        IsShiftBy.comp'_self_left_inv]
    _ = s.shiftMap u 0
        (IsShiftBy.compare (IsShiftBy.self ((Z0.of (DGFunctor C D) F).obj X)) t) :=
      hmap.symm

/-- Additive comparisons at propositionally equal total degrees differ only by
the corresponding `eqToHom`. -/
lemma z0ShiftFunctorAddIso'_hom_app_congr (n m nm nm' : ℤ)
    (h : n + m = nm) (h' : n + m = nm') (F : Z0 (DGFunctor C D)) :
    (z0ShiftFunctorAddIso' (C := C) (D := D) n m nm h).hom.app F =
      eqToHom (congrArg (fun k => (z0ShiftFunctor (C := C) (D := D) k).obj F)
        (show nm = nm' by omega)) ≫
        (z0ShiftFunctorAddIso' n m nm' h').hom.app F := by
  obtain rfl : nm = nm' := by omega
  rw [eqToHom_refl, Category.id_comp]

/-- Associativity of the additive comparison, in the exact component form
required by `ShiftMkCore`.

The inverse of the left-hand composite is `shiftedFunctorAddAssocLeft`; the
inverse of the right-hand composite is `shiftedFunctorAddAssocRight`. Thus
this is `shiftedFunctorAdd_assoc`, transported once through `Iso.symm`, rather
than a second pointwise associativity proof. -/
lemma z0ShiftFunctorAddIso'_assoc (n m k nm mk r : ℤ)
    (hnm : n + m = nm) (hmk : m + k = mk)
    (hleft : nm + k = r) (hright : n + mk = r)
    (F : Z0 (DGFunctor C D)) :
    (z0ShiftFunctorAddIso' (C := C) (D := D) nm k r hleft).hom.app F ≫
        (z0ShiftFunctor k).map
          ((z0ShiftFunctorAddIso' n m nm hnm).hom.app F) =
      (z0ShiftFunctorAddIso' n mk r hright).hom.app F ≫
        (z0ShiftFunctorAddIso' m k mk hmk).hom.app
          ((z0ShiftFunctor n).obj F) := by
  let eleft :=
    (z0ShiftFunctorAddIso' (C := C) (D := D) nm k r hleft).app F ≪≫
      (z0ShiftFunctor k).mapIso
        ((z0ShiftFunctorAddIso' n m nm hnm).app F)
  let eright :=
    (z0ShiftFunctorAddIso' (C := C) (D := D) n mk r hright).app F ≪≫
      (z0ShiftFunctorAddIso' m k mk hmk).app ((z0ShiftFunctor n).obj F)
  change eleft.hom = eright.hom
  have hinv : eleft.inv = eright.inv := by
    apply Subtype.ext
    exact (Z0.of (DGFunctor C D) F).shiftedFunctorAdd_assoc
      n m k nm mk r hnm hmk hleft hright
  have hsymm : eleft.symm = eright.symm := Iso.ext hinv
  have hiso : eleft = eright := by
    calc
      eleft = eleft.symm.symm := (Iso.symm_symm_eq eleft).symm
      _ = eright.symm.symm := congrArg Iso.symm hsymm
      _ = eright := Iso.symm_symm_eq eright
  exact congrArg Iso.hom hiso

/-- The explicit shifted dg functors and their canonical comparisons, packaged
as Mathlib shift data on the closed category of dg functors. -/
noncomputable def z0ShiftMkCore : ShiftMkCore (Z0 (DGFunctor C D)) ℤ where
  F := z0ShiftFunctor
  zero := z0ShiftFunctorZeroIso
  add := z0ShiftFunctorAddIso
  assoc_hom_app n m k F := by
    rw [z0ShiftFunctorAddIso, z0ShiftFunctorAddIso, z0ShiftFunctorAddIso,
      z0ShiftFunctorAddIso,
      z0ShiftFunctorAddIso'_assoc n m k (n + m) (m + k) (n + m + k)
        rfl rfl rfl (by omega) F,
      z0ShiftFunctorAddIso'_hom_app_congr n (m + k) (n + m + k)
        (n + (m + k)) (by omega) (by omega) F,
      Category.assoc]
  zero_add_hom_app n F :=
    z0ShiftFunctorAddIso'_hom_app_zero_left n (0 + n) rfl F
  add_zero_hom_app n F :=
    z0ShiftFunctorAddIso'_hom_app_zero_right n (n + 0) rfl F

/-- **Closed dg functors have the pointwise dg shift as a Mathlib
`HasShift`.** -/
noncomputable instance z0HasShift : HasShift (Z0 (DGFunctor C D)) ℤ :=
  hasShiftMk _ _ (z0ShiftMkCore (C := C) (D := D))

/-- The ambient shift functor is the pointwise shifted dg functor. -/
lemma z0_shiftFunctor_eq (n : ℤ) :
    CategoryTheory.shiftFunctor (Z0 (DGFunctor C D)) n =
      z0ShiftFunctor (C := C) (D := D) n := by
  rw [ShiftMkCore.shiftFunctor_eq]
  rfl

/-- The object selected by the ambient shift is `DGFunctor.shiftedFunctor`. -/
@[simp]
lemma z0_shiftFunctor_obj (n : ℤ) (F : Z0 (DGFunctor C D)) :
    (CategoryTheory.shiftFunctor (Z0 (DGFunctor C D)) n).obj F =
      (Z0.of (DGFunctor C D) F).shiftedFunctor n := by
  rw [z0_shiftFunctor_eq]
  rfl

/-- The ambient zero comparison is the dg zero-shift comparison. -/
lemma z0_shiftFunctorZero_eq :
    CategoryTheory.shiftFunctorZero (Z0 (DGFunctor C D)) ℤ =
      z0ShiftFunctorZeroIso (C := C) (D := D) := by
  rw [ShiftMkCore.shiftFunctorZero_eq]
  rfl

/-- The ambient additive comparison is the dg additive comparison. -/
lemma z0_shiftFunctorAdd_eq (n m : ℤ) :
    CategoryTheory.shiftFunctorAdd (Z0 (DGFunctor C D)) n m =
      z0ShiftFunctorAddIso (C := C) (D := D) n m := by
  rw [ShiftMkCore.shiftFunctorAdd_eq]
  rfl

end DGFunctor

end CategoryTheory
