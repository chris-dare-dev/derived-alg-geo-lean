/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.Pretriangulated

/-!
# The model shift is Mathlib's shift

`Cdg.isShiftBy K n` exhibits `K⟦n⟧` as a shift of `K` in the dg sense: the
witness is the canonical closed cochain `Cdg.shiftCocycle K n` of degree `-n`,
and nothing about `HasShift (CochainComplex A ℤ) ℤ` enters that statement. This
file proves that the dg notion really does restrict to the categorical one, in
the three forms `dg-enhancements-e7` needs before `Functor.CommShift` can be
built for the seam:

* `Cdg.mapShift_isShiftBy` -- the dg action of the shift on a *morphism* is
  `φ ↦ φ⟦n⟧'`;
* `Cdg.shiftCocycle_zero` -- the degree-`0` witness is `shiftFunctorZero`;
* `Cdg.comp_shiftCocycle` -- composing the witnesses for `a` and `b` is the
  witness for `a + b`, corrected by `shiftFunctorAdd`.

The last two are exactly the two coherence identities a `CommShift` structure
asks for, transcribed into the dg model. That they hold on the nose, with no
sign, is because `Cochain.rightShift` carries none: the Koszul sign of the shift
lives on `Cochain.leftShift`, which shifts the *source* of a cochain, and
`shiftCocycle` shifts the target.

## Why the work is done on `CochainComplex A ℤ` and transferred afterwards

`Cdg A` is a type synonym for `CochainComplex A ℤ` and `Cdg.of` is the
identity, so `of A (shiftObj K a)` and `(of A K)⟦a⟧` are the same term -- but
only after unfolding two definitions, which `rw` will not do while it builds a
motive. A component computation phrased on `Cdg` therefore produces goals that
are ill-typed at `instances` transparency and no rewrite fires.

`rightShift_id_zero` and `rightShift_id_comp` are consequently stated on plain
cochain complexes, where every object is one opaque term, and the `Cdg`-level
statements are read off them by term elaboration, which crosses the synonym
where tactic matching does not.

## Everything is `XIsoOfEq`, and that is the point

Each identity is, degreewise, an equality between composites of identity-like
maps between components indexed by integers that `omega` proves equal. There is
no homological content here; the content is that the two indexings agree, which
is what makes the seam's shift comparison exist at all.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open CochainComplex CochainComplex.HomComplex

namespace Cdg

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-! ## On plain cochain complexes -/

/-- **The degree-zero canonical cochain is `shiftFunctorZero`.** Stated on a
plain cochain complex; `Cdg.shiftCocycle_zero` is the same statement read on
`C^dg`. -/
lemma rightShift_id_zero (K : CochainComplex A ℤ) :
    (Cochain.ofHom (𝟙 K)).rightShift 0 (-0) (by omega) =
      Cochain.ofHom ((shiftFunctorZero (CochainComplex A ℤ) ℤ).inv.app K) := by
  ext p q hpq
  obtain rfl : q = p := by omega
  conv_lhs => rw [Cochain.rightShift_v _ 0 (-0) (by omega) q q hpq q (add_zero q)]
  simp [Cochain.ofHom_v, CochainComplex.shiftFunctorZero_inv_app_f,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]

/-- **The canonical cochains compose, up to `shiftFunctorAdd`.** Stated on a
plain cochain complex; `Cdg.comp_shiftCocycle` is the same statement read on
`C^dg`.

The type ascription on the second factor of the right-hand side is
load-bearing: without it that composite's target elaborates as
`(shiftFunctor a ⋙ shiftFunctor b).obj K` while the left-hand side's is
`(shiftFunctor b).obj ((shiftFunctor a).obj K)`, and the two -- definitionally
equal -- forms block every rewrite. -/
lemma rightShift_id_comp (K : CochainComplex A ℤ) (a b : ℤ) :
    Cochain.comp ((Cochain.ofHom (𝟙 K)).rightShift a (-a) (by omega))
        ((Cochain.ofHom (𝟙 (K⟦a⟧ : CochainComplex A ℤ))).rightShift b (-b) (by omega))
        (show -a + -b = -(a + b) by omega) =
      Cochain.comp ((Cochain.ofHom (𝟙 K)).rightShift (a + b) (-(a + b)) (by omega))
        (Cochain.ofHom (show (K⟦a + b⟧ : CochainComplex A ℤ) ⟶
            (((K⟦a⟧ : CochainComplex A ℤ))⟦b⟧ : CochainComplex A ℤ) from
          (shiftFunctorAdd (CochainComplex A ℤ) a b).hom.app K))
        (show -(a + b) + 0 = -(a + b) by omega) := by
  ext p q hpq
  rw [Cochain.comp_v _ _ (show -a + -b = -(a + b) by omega) p (p + -a) q rfl (by omega),
    Cochain.comp_zero_cochain_v,
    Cochain.rightShift_v _ a (-a) (by omega) p (p + -a) rfl p (add_zero p),
    Cochain.rightShift_v _ b (-b) (by omega) (p + -a) q (by omega) (p + -a) (add_zero _),
    Cochain.rightShift_v _ (a + b) (-(a + b)) (by omega) p q hpq p (add_zero p),
    Cochain.ofHom_v]
  simp [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq,
    CochainComplex.shiftFunctorAdd_hom_app_f]

/-- Right composition with the canonical shift cochain is `Cochain.rightShift`. -/
lemma comp_shiftCocycle_id {M N : CochainComplex A ℤ} {n : ℤ} (γ : Cochain M N n)
    (a n' : ℤ) (hn' : n' + a = n) :
    Cochain.comp γ ((Cochain.ofHom (𝟙 N)).rightShift a (-a) (by omega))
        (show n + -a = n' by omega) = γ.rightShift a n' hn' := by
  ext p q hpq
  rw [Cochain.comp_v _ _ (show n + -a = n' by omega) p (p + n) q rfl (by omega),
    Cochain.rightShift_v _ a (-a) (by omega) (p + n) q (by omega) (p + n) (add_zero _),
    Cochain.rightShift_v γ a n' hn' p q hpq (p + n) rfl, Cochain.ofHom_v]
  simp only [HomologicalComplex.id_f, Category.id_comp]
  rfl

/-! ## On `C^dg` -/

/-- The canonical shift cochain, degreewise: the identity-like map from `K` in
degree `p` to `K⟦n⟧` in degree `q`, where `q + n = p`. -/
lemma shiftCocycle_v (K : Cdg A) (n p q : ℤ) (hpq : p + -n = q) :
    (shiftCocycle K n).1.v p q hpq =
      eqToHom (show (of A K).X p = ((of A K)⟦n⟧ : CochainComplex A ℤ).X q from by
        rw [CochainComplex.shiftFunctor_obj_X']; congr 1; omega) := by
  rw [shiftCocycle, Cocycle.rightShift_coe,
    Cochain.rightShift_v _ n (-n) (by omega) p q hpq p (add_zero p)]
  simp [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]

/-- **The dg shift acts on morphisms as `⟦n⟧'`.** `mapShift` is built from
`IsShiftBy.inv`, which is `Classical.choice`; `IsShiftBy.mapShift_unique`
reduces the identification to the naturality square of `shiftCocycle`, and that
is degreewise an equality of two identity maps. -/
lemma mapShift_isShiftBy {K L : Cdg A} (n : ℤ) (φ : of A K ⟶ of A L) :
    IsShiftBy.mapShift (isShiftBy K n) (isShiftBy L n) (Cochain.ofHom φ) =
      Cochain.ofHom (φ⟦n⟧') := by
  refine IsShiftBy.mapShift_unique _ _ _ _ ?_
  show Cochain.comp (shiftCocycle K n).1 (Cochain.ofHom (φ⟦n⟧'))
      (show -n + 0 = -n by omega) =
    Cochain.comp (Cochain.ofHom φ) (shiftCocycle L n).1 (show 0 + -n = -n by omega)
  ext p q hpq
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    shiftCocycle_v K n p q hpq, shiftCocycle_v L n p q hpq]
  obtain rfl : p = q + n := by omega
  simp [CochainComplex.shiftFunctor_map_f']

/-- **The degree-zero witness is `shiftFunctorZero`.** -/
lemma shiftCocycle_zero (K : Cdg A) :
    (shiftCocycle K 0).1 =
      Cochain.ofHom ((shiftFunctorZero (CochainComplex A ℤ) ℤ).inv.app (of A K)) :=
  rightShift_id_zero (of A K)

/-- **The witnesses compose, up to `shiftFunctorAdd`.** Composing the witness
for `a` with the witness for `b` on `K⟦a⟧` is the witness for `a + b`, followed
by Mathlib's comparison `K⟦a + b⟧ ≅ (K⟦a⟧)⟦b⟧`. -/
lemma comp_shiftCocycle (K : Cdg A) (a b : ℤ) :
    Cochain.comp (shiftCocycle K a).1 (shiftCocycle (shiftObj K a) b).1
        (show -a + -b = -(a + b) by omega) =
      Cochain.comp (shiftCocycle K (a + b)).1
        (Cochain.ofHom ((shiftFunctorAdd (CochainComplex A ℤ) a b).hom.app (of A K)))
        (show -(a + b) + 0 = -(a + b) by omega) :=
  rightShift_id_comp (of A K) a b

end Cdg

end CategoryTheory
