/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Basic
import DerivedAlgGeo.Algebra.Homology.DGCategory.Shift

/-!
# `IsShiftBy` really is a shift of hom-complexes

`Pretriangulated.lean` says, in prose, that `Y` is a shift of `X` by `n` when
`dgHom W Y ≅ (dgHom W X)⟦n⟧` naturally in `W`. What `IsShiftBy` actually
carries is weaker on its face: a closed element `ε` of degree `-n` such that
right composition with it is **bijective in each degree**. Degreewise
bijections are not an isomorphism of complexes, so the sentence is a gloss
until someone supplies the differentials.

This file supplies them, and the point is that the Koszul sign is what makes it
work. Leibniz gives

`δ (f · ε) = f · (δ ε) + (-1) ^ (-n) • (δ f) · ε`

and `ε` is closed, so `δ (f · ε) = (-1) ^ (-n) • (δ f) · ε`. Right composition
with `ε` therefore does **not** commute with the differentials — it commutes
with them up to `(-1) ^ (-n)`. That is exactly the sign `shiftD` carries, so
`compRight` is a map of complexes into the *shifted* hom-complex and into no
other. The two `(-1) ^ (-n)` cancel because a unit squares to one, which is the
whole proof of `compRight_comm`.

So `Shift.lean`'s sign is not decoration on a definition: it is what makes
`IsShiftBy`'s degreewise data assemble into the isomorphism its docstring
claims.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

/-- **Right composition with a closed element of degree `-n` is a map of
complexes into the `(-n)`-shifted hom-complex.** It is not a map into the
unshifted one: Leibniz leaves a factor `(-1) ^ (-n)`, and `shiftD (-n)` is
where that factor is absorbed. -/
lemma compRight_comm {X Y : C} {n : ℤ} {ε : (dgHom X Y).X (-n)}
    (hε : ((dgHom X Y).d (-n) (-n + 1)).hom ε = 0) (W : C) (p p' q q' : ℤ)
    (hq : p + -n = q) (hq' : p' + -n = q') (hp : p + 1 = p')
    (f : (dgHom W X).X p) :
    shiftD (-n) q q' (compRight W ε p q hq f) =
      compRight W ε p' q' hq' (((dgHom W X).d p p').hom f) := by
  subst hp
  simp only [shiftD_apply, compRight_apply]
  rw [dgComp_leibniz p (-n) q q' hq (by omega) f ε, hε, map_zero, zero_add,
    smul_smul, ← Int.negOnePow_add, show (-n + -n) = 2 * (-n) by ring,
    Int.negOnePow_two_mul, one_smul]

/-- The morphism of complexes underlying `IsShiftBy`: right composition with the
structure element, landing in the shifted hom-complex. -/
noncomputable def IsShiftBy.homMap {X Y : C} {n : ℤ} (h : IsShiftBy X n Y) (W : C) :
    dgHom W X ⟶ (dgHom W Y)⟦-n⟧ where
  f p := AddCommGrpCat.ofHom (compRight W h.hom p (p + -n) rfl)
  comm' p p' hpp' := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    show shiftD (-n) (p + -n) (p' + -n) (compRight W h.hom p (p + -n) rfl f) = _
    exact compRight_comm h.hom_closed W p p' (p + -n) (p' + -n) rfl rfl hpp' f

/-- Each component of `IsShiftBy.homMap` is bijective — this is the structure's
own `bijective` field, restated at the degree the shifted complex uses. -/
lemma IsShiftBy.bijective_homMap {X Y : C} {n : ℤ} (h : IsShiftBy X n Y) (W : C) (p : ℤ) :
    Function.Bijective ((h.homMap W).f p).hom :=
  h.bijective W p (p + -n) rfl

end CategoryTheory
