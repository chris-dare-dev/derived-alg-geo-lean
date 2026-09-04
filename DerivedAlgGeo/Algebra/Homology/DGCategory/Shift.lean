/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Tactic.Ring
import DerivedAlgGeo.Algebra.Homology.DGCategory.Basic

/-!
# Shifted hom-complexes

For a dg category `C`, each hom-complex `dgHom X Y` can be shifted by `m : ℤ`
using Mathlib's shift on `CochainComplex`. This file records what survives that
shift: the differential picks up `(-1) ^ m`, and composition still satisfies
Leibniz, associativity, and the unit laws — provided it picks up a Koszul sign.

This is the shift `dg-enhancements-e2`'s summary claimed to deliver and did not;
`dg-enhancements-e5` (#376) owns it, and the roadmap is corrected alongside.

## The sign is derived, not chosen

Mathlib's `CochainComplex.shiftFunctor m` sends `K` to the complex that is
`K.X (i + m)` in degree `i`, with differential `m.negOnePow • K.d _ _`
(`shiftFunctor_obj_X'`, `shiftFunctor_obj_d'`, both `rfl` at the pin). Take
`f` of shifted degree `p` in `(dgHom X Y)⟦m⟧` and `g` of shifted degree `q` in
`(dgHom Y Z)⟦n⟧`, and ask for a composition `ε • dgComp` making the Leibniz
rule of `DGCategory` hold verbatim in the shifted complexes. Matching the two
terms separately forces

* `ε (p, q + 1) = (-1) ^ m * ε (p, q)`, from the term carrying `δ g`;
* `ε (p + 1, q) = ε (p, q)`, from the term carrying `δ f`.

So `ε` cannot depend on `p`, and `ε = (-1) ^ (q * m)` is the solution. The sign
is the degree of the element that moves times the shift it moves past, which is
the Koszul rule — but it is written here as the *conclusion* of the two matching
conditions rather than as an appeal to that rule.

Associativity and the unit laws are then automatic rather than further
constraints; `shiftComp_assoc` and the two `dgId` lemmas below confirm this.

## Raw degrees, not shifted ones

Every degree argument below is the degree in the *underlying* hom-complex, and
the shift enters only through the sign. Writing `shiftComp` on shifted degrees
instead — with hom-types like `(dgHom X Y).X (p + m)` — costs a rewrite between
`(q + 1) + n` and `(q + n) + 1` in the Leibniz proof, and rewriting an index of
`HomologicalComplex.X` breaks the motive. On raw degrees the statement has the
same shape as `dgComp` itself: three degrees and one equation. The shifted
degree is recovered as `b - n`, which is where the sign's `b - n` comes from.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct

namespace DGCategory

variable {C : Type u} [DGCategory.{v} C]

/-- The differential of the `m`-shifted hom-complex, at raw degrees. -/
def shiftD (m : ℤ) {X Y : C} (a b : ℤ) :
    (dgHom X Y).X a →+ (dgHom X Y).X b :=
  m.negOnePow • ((dgHom X Y).d a b).hom

/-- Composition of shifted hom-complexes: `dgComp` with the Koszul sign that the
two Leibniz matching conditions force. `m` and `n` are the shifts of the source
and middle hom-complexes; `b - n` is the degree of the second argument in the
shifted complex. -/
def shiftComp (m n : ℤ) {X Y Z : C} (a b c : ℤ) (h : a + b = c) :
    (dgHom X Y).X a →+ (dgHom Y Z).X b →+ (dgHom X Z).X c :=
  ((b - n) * m).negOnePow • dgComp a b c h

/-- `shiftD` applied to an element, unfolded. -/
lemma shiftD_apply (m : ℤ) {X Y : C} (a b : ℤ) (f : (dgHom X Y).X a) :
    shiftD m a b f = m.negOnePow • ((dgHom X Y).d a b).hom f := rfl

/-- `shiftComp` applied to a pair of elements, unfolded. -/
lemma shiftComp_apply (m n : ℤ) {X Y Z : C} (a b c : ℤ) (h : a + b = c)
    (f : (dgHom X Y).X a) (g : (dgHom Y Z).X b) :
    shiftComp m n a b c h f g = ((b - n) * m).negOnePow • dgComp a b c h f g := rfl

/-- The unshifted case is the original composition, on the nose. -/
lemma shiftComp_zero_zero {X Y Z : C} (a b c : ℤ) (h : a + b = c) :
    shiftComp (X := X) (Y := Y) (Z := Z) 0 0 a b c h = dgComp a b c h := by
  simp [shiftComp]

/-- The unshifted differential is the original differential. -/
lemma shiftD_zero {X Y : C} (a b : ℤ) :
    shiftD (C := C) (X := X) (Y := Y) 0 a b = ((dgHom X Y).d a b).hom := by
  simp [shiftD]

/-! ### The tie-back to Mathlib's shift

`shiftD` and the shifted hom-types are not a private convention: they are what
`CochainComplex.shiftFunctor` already does, and both lemmas below are `rfl`. -/

/-- Degree `p` of the `m`-shifted hom-complex is degree `p + m` of the original.
This is `CochainComplex.shiftFunctor`'s own indexing, so the lemma is `rfl`. -/
lemma shiftFunctor_dgHom_X (m : ℤ) {X Y : C} (p : ℤ) :
    (((dgHom X Y))⟦m⟧).X p = (dgHom X Y).X (p + m) := rfl

/-- `shiftD` *is* the differential of the shifted hom-complex, not a lookalike:
the lemma is `rfl`, so the `(-1) ^ m` in `shiftD` is Mathlib's sign rather than a
convention this file introduces. -/
lemma shiftFunctor_dgHom_d (m : ℤ) {X Y : C} (p p' : ℤ) :
    ((((dgHom X Y))⟦m⟧).d p p').hom = shiftD m (p + m) (p' + m) := rfl

/-! ### The four laws -/

/-- A morphism of `AddCommGrpCat` commutes with the `ℤˣ` action, which factors
through `ℤ`. Restated here so the sign bookkeeping can stay in `ℤˣ`. -/
private lemma hom_units_smul' {M N : AddCommGrpCat.{v}} (φ : M ⟶ N) (u : ℤˣ) (x : M) :
    φ.hom (u • x) = u • φ.hom x := by
  simp [Units.smul_def, map_zsmul]

private lemma dgComp_units_smul_left' {X Y Z : C} (a b c : ℤ) (h : a + b = c) (u : ℤˣ)
    (f : (dgHom X Y).X a) (g : (dgHom Y Z).X b) :
    dgComp a b c h (u • f) g = u • dgComp a b c h f g := by
  simp [Units.smul_def, map_zsmul]

private lemma dgComp_units_smul_right' {X Y Z : C} (a b c : ℤ) (h : a + b = c) (u : ℤˣ)
    (f : (dgHom X Y).X a) (g : (dgHom Y Z).X b) :
    dgComp a b c h f (u • g) = u • dgComp a b c h f g := by
  simp [Units.smul_def, map_zsmul]

/-- **The Leibniz rule survives the shift**, in the same shape as the axiom: the
sign on the second term is the degree of the first argument's partner in the
*shifted* complex, `b - n`. This is the lemma the sign was solved for. -/
lemma shiftComp_leibniz (m n : ℤ) {X Y Z : C} (a b c c' : ℤ) (h : a + b = c) (hc : c + 1 = c')
    (f : (dgHom X Y).X a) (g : (dgHom Y Z).X b) :
    shiftD (m + n) c c' (shiftComp m n a b c h f g) =
      shiftComp m n a (b + 1) c' (by omega) f (shiftD n b (b + 1) g) +
        (b - n).negOnePow • shiftComp m n (a + 1) b c' (by omega) (shiftD m a (a + 1) f) g := by
  simp only [shiftD_apply, shiftComp_apply, hom_units_smul',
    dgComp_units_smul_left', dgComp_units_smul_right', smul_smul, ← Int.negOnePow_add]
  rw [dgComp_leibniz a b c c' h hc f g, smul_add, smul_smul, ← Int.negOnePow_add]
  congr 1
  · rw [show ((b + 1 - n) * m + n) = (m + n + (b - n) * m) by ring]
  · rw [show (m + n + (b - n) * m + b) = (b - n + ((b - n) * m + m)) + 2 * n by ring,
      Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- Associativity survives the shift with no further sign condition: the two
sides carry `(b - n) * m + (d - l) * (m + n)` and
`(d - l) * n + (b + d - (n + l)) * m`, which are equal as integers. -/
lemma shiftComp_assoc (m n l : ℤ) {W X Y Z : C} (a b d ab bd abd : ℤ)
    (hab : a + b = ab) (hbd : b + d = bd) (habd : ab + d = abd)
    (f : (dgHom W X).X a) (g : (dgHom X Y).X b) (k : (dgHom Y Z).X d) :
    shiftComp (m + n) l ab d abd habd (shiftComp m n a b ab hab f g) k =
      shiftComp m (n + l) a bd abd (by omega) f (shiftComp n l b d bd hbd g k) := by
  simp only [shiftComp_apply, dgComp_units_smul_left', dgComp_units_smul_right',
    smul_smul, ← Int.negOnePow_add]
  rw [dgComp_assoc a b d ab bd abd hab hbd habd f g k,
    show ((d - l) * (m + n) + (b - n) * m) = ((bd - (n + l)) * m + (d - l) * n) by
      subst hbd; ring]

/-- The identity is a left unit for the shifted composition. Its hom-complex is
unshifted, so the sign is `((b - n) * 0)` and vanishes. -/
lemma shiftComp_dgId_left (n : ℤ) {X Y : C} (b : ℤ) (g : (dgHom X Y).X b) :
    shiftComp 0 n 0 b b (zero_add b) (dgId X) g = g := by
  simp [shiftComp_apply, dgId_comp]

/-- The identity is a right unit for the shifted composition. It sits in degree
`0` of an unshifted complex, so the sign is `((0 - 0) * m)` and vanishes. -/
lemma shiftComp_dgId_right (m : ℤ) {X Y : C} (a : ℤ) (f : (dgHom X Y).X a) :
    shiftComp m 0 a 0 a (add_zero a) f (dgId Y) = f := by
  simp [shiftComp_apply, dgComp_id]

/-- The shifted differential still squares to zero: the two signs cancel. No
hypothesis relates `a`, `b`, `c` — off the diagonal `d` is zero by `shape`, so
the statement holds for every triple. -/
lemma shiftD_shiftD (m : ℤ) {X Y : C} (a b c : ℤ) (f : (dgHom X Y).X a) :
    shiftD m b c (shiftD m a b f) = 0 := by
  have hd : ((dgHom X Y).d a b) ≫ ((dgHom X Y).d b c) = 0 :=
    (dgHom X Y).d_comp_d a b c
  simp only [shiftD_apply, hom_units_smul', smul_smul, ← Int.negOnePow_add]
  rw [show (m + m) = 2 * m by ring, Int.negOnePow_two_mul]
  have : ((dgHom X Y).d b c).hom (((dgHom X Y).d a b).hom f) = 0 := by
    rw [← AddCommGrpCat.comp_apply, hd]
    simp
  rw [this, smul_zero]

end DGCategory

end CategoryTheory
