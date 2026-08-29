/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Enriched.DGCategory.Pretriangulated.Cone

/-!
# Rotating a cone triangle

`dg-enhancements-e6`. The rotation axiom asks that `Y → Z → X⟦1⟧ → Y⟦1⟧` be
distinguished whenever `X → Y → Z → X⟦1⟧` is. Since a distinguished triangle is
one isomorphic to a *cone* triangle, what has to be produced is a comparison
between a cone on `inr : Y → Z` and the shift `X⟦1⟧`.

## `X⟦1⟧` is not a cone on `inr`, and cannot be made one

`IsConeOf` is a representability condition on the nose: maps into the cone split
*bijectively* in every degree. For a cone `W` on `inr`, that reads
`Hom(V, Y)⟨1⟩ × Hom(V, Z) ≅ Hom(V, W)`, and `Z` itself already splits as
`Hom(V, X)⟨1⟩ × Hom(V, Y)`. So `W` is three summands wide and `X⟦1⟧` is one; they
are not isomorphic as graded objects, and no choice of structure will make them so.

They *are* homotopy equivalent, which is all `H⁰` sees, and that is what this file
constructs: a pair of closed degree-zero maps between `W` and `X⟦1⟧`. The two
extra summands of `W` cancel in `H⁰` rather than being absent.

## The maps

`fwd = snd_W ≫ toShift`. Closed because `δ snd_W = -(fst_W ≫ inr)` — the cone's
one differential correction — and `inr ≫ toShift = 0`, which is the triangle
composing to zero at its second vertex. The correction is killed by the
orthogonality rather than by a choice.

`bwd` has to be assembled against the splitting, and its `inl_W`-component is
forced. Take `s.inv ≫ inl` for the `inr_W`-component: it is not closed, its
differential is `s.inv ≫ f ≫ inr`. The `inl_W`-component `-(s.inv ≫ f)`
contributes exactly `-(s.inv ≫ f ≫ inr)` through `δ inl_W = inr ≫ inr_W`, and its
own differential vanishes because `s.inv` and `f` are both closed. So the sum is
closed, and the sign is solved for rather than guessed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

namespace IsConeOf

variable {X Y Z W X' : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z)
  (hd : IsConeOf hc.inr W) (s : IsShiftBy X 1 X')

/-- The comparison `Cone(inr) ⟶ X⟦1⟧`: project to `Z`, then take the connecting
morphism of the original cone. -/
noncomputable def rotateFwd : (dgHom W X').X 0 :=
  dgComp 0 0 0 (by omega) hd.snd (hc.toShift s)

/-- It is closed. `δ snd_W` is the cone's correction term `-(fst_W ≫ inr)`, and
`inr ≫ toShift = 0` kills it. -/
lemma rotateFwd_closed : ((dgHom W X').d 0 1).hom (hc.rotateFwd hd s) = 0 := by
  have hleib : ((dgHom W X').d 0 1).hom
        (dgComp 0 0 0 (by omega) hd.snd (hc.toShift s)) =
      dgComp 0 1 1 (by omega) hd.snd (((dgHom Z X').d 0 1).hom (hc.toShift s)) +
        (0 : ℤ).negOnePow •
          dgComp 1 0 1 (by omega) (((dgHom W Z).d 0 1).hom hd.snd) (hc.toShift s) :=
    dgComp_leibniz (X := W) (Y := Z) (Z := X') 0 0 0 1 (by omega) (by omega)
      hd.snd (hc.toShift s)
  rw [rotateFwd, hleib, hc.toShift_closed s, hd.delta_snd, Int.negOnePow_zero, one_smul]
  simp only [map_zero, map_neg, AddMonoidHom.neg_apply, zero_add]
  rw [dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega), hc.inr_comp_toShift s]
  simp

/-- The comparison `X⟦1⟧ ⟶ Cone(inr)`, assembled against the splitting of maps
into the cone. -/
noncomputable def rotateBwd : (dgHom X' W).X 0 :=
  dgComp 1 (-1) 0 (by omega) (-dgComp 1 0 1 (by omega) s.inv f) hd.inl +
    dgComp 0 0 0 (by omega) (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) hd.inr

include hc in
/-- The `inl_W`-component's own differential vanishes: `s.inv` is closed by
`IsShiftBy.inv_closed`, and `f` is closed by `IsConeOf.delta_f`. -/
lemma delta_shiftInvComp :
    ((dgHom X' Y).d 1 2).hom (dgComp 1 0 1 (by omega) s.inv f) = 0 := by
  have hleib : ((dgHom X' Y).d 1 2).hom (dgComp 1 0 1 (by omega) s.inv f) =
      dgComp 1 1 2 (by omega) s.inv (((dgHom X Y).d 0 1).hom f) +
        (0 : ℤ).negOnePow •
          dgComp 2 0 2 (by omega) (((dgHom X' X).d 1 2).hom s.inv) f :=
    dgComp_leibniz (X := X') (Y := X) (Z := Y) 1 0 1 2 (by omega) (by omega) s.inv f
  have hinv : ((dgHom X' X).d 1 2).hom s.inv = 0 := s.inv_closed
  rw [hleib, hc.delta_f, hinv]
  simp

/-- The `inr_W`-component is not closed, and this is its differential. -/
lemma delta_shiftInvComp_inl :
    ((dgHom X' Z).d 0 1).hom (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) =
      dgComp 1 0 1 (by omega) s.inv (dgComp 0 0 0 (by omega) f hc.inr) := by
  have hleib : ((dgHom X' Z).d 0 1).hom (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) =
      dgComp 1 0 1 (by omega) s.inv (((dgHom X Z).d (-1) 0).hom hc.inl) +
        (-1 : ℤ).negOnePow •
          dgComp 2 (-1) 1 (by omega) (((dgHom X' X).d 1 2).hom s.inv) hc.inl :=
    dgComp_leibniz (X := X') (Y := X) (Z := Z) 1 (-1) 0 1 (by omega) (by omega)
      s.inv hc.inl
  have hinv : ((dgHom X' X).d 1 2).hom s.inv = 0 := s.inv_closed
  rw [hleib, hc.δ_inl, hinv]
  simp

/-- **The backward comparison is closed.** The two components' differentials are
the same element of `Hom(X⟦1⟧, W)` with opposite signs: the `inl_W`-component
contributes through `δ inl_W = inr ≫ inr_W`, the `inr_W`-component through its
own failure to be closed. The sign in `rotateBwd` is what makes them cancel. -/
lemma rotateBwd_closed : ((dgHom X' W).d 0 1).hom (hc.rotateBwd hd s) = 0 := by
  have hleib₁ : ((dgHom X' W).d 0 1).hom
        (dgComp 1 (-1) 0 (by omega) (-dgComp 1 0 1 (by omega) s.inv f) hd.inl) =
      dgComp 1 0 1 (by omega) (-dgComp 1 0 1 (by omega) s.inv f)
          (((dgHom Y W).d (-1) 0).hom hd.inl) +
        (-1 : ℤ).negOnePow • dgComp 2 (-1) 1 (by omega)
          (((dgHom X' Y).d 1 2).hom (-dgComp 1 0 1 (by omega) s.inv f)) hd.inl :=
    dgComp_leibniz (X := X') (Y := Y) (Z := W) 1 (-1) 0 1 (by omega) (by omega) _ hd.inl
  have hleib₂ : ((dgHom X' W).d 0 1).hom
        (dgComp 0 0 0 (by omega) (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) hd.inr) =
      dgComp 0 1 1 (by omega) (dgComp 1 (-1) 0 (by omega) s.inv hc.inl)
          (((dgHom Z W).d 0 1).hom hd.inr) +
        (0 : ℤ).negOnePow • dgComp 1 0 1 (by omega)
          (((dgHom X' Z).d 0 1).hom (dgComp 1 (-1) 0 (by omega) s.inv hc.inl)) hd.inr :=
    dgComp_leibniz (X := X') (Y := Z) (Z := W) 0 0 0 1 (by omega) (by omega) _ hd.inr
  rw [rotateBwd, map_add, hleib₁, hleib₂, hd.δ_inl, hd.inr_closed]
  simp only [map_neg, AddMonoidHom.neg_apply, map_zero, zero_add]
  rw [hc.delta_shiftInvComp s, hc.delta_shiftInvComp_inl s, Int.negOnePow_zero, one_smul]
  simp only [neg_zero, map_zero, AddMonoidHom.zero_apply, smul_zero, add_zero]
  rw [← dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega) s.inv f hc.inr,
    dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega)
      (dgComp 1 0 1 (by omega) s.inv f) hc.inr hd.inr]
  abel

section Composites

/-- `inl_W` followed by the forward comparison vanishes: `inl_W ≫ snd_W = 0`. -/
lemma inl_comp_rotateFwd :
    dgComp (-1) 0 (-1) (by omega) hd.inl (hc.rotateFwd hd s) = 0 := by
  rw [rotateFwd, ← dgComp_assoc (-1) 0 0 (-1) 0 (-1) (by omega) (by omega) (by omega),
    hd.inl_comp_snd]
  simp

/-- `inr_W` followed by the forward comparison is the connecting morphism:
`inr_W ≫ snd_W = dgId`. -/
lemma inr_comp_rotateFwd :
    dgComp 0 0 0 (by omega) hd.inr (hc.rotateFwd hd s) = hc.toShift s := by
  rw [rotateFwd, ← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega),
    hd.inr_comp_snd, dgId_comp]

/-- **One composite is the identity on the nose.** No homotopy is needed in this
direction: the `inl_W`-component of `rotateBwd` dies against `snd_W`, and what
survives is `s.inv ≫ (inl ≫ fst) ≫ s.hom`, which is `s.inv ≫ s.hom`. -/
lemma rotateBwd_comp_rotateFwd :
    dgComp 0 0 0 (by omega) (hc.rotateBwd hd s) (hc.rotateFwd hd s) = dgId X' := by
  rw [rotateBwd, map_add, AddMonoidHom.add_apply,
    dgComp_assoc 1 (-1) 0 0 (-1) 0 (by omega) (by omega) (by omega),
    dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega),
    hc.inl_comp_rotateFwd hd s, hc.inr_comp_rotateFwd hd s]
  simp only [map_zero, zero_add]
  rw [toShift,
    dgComp_assoc 1 (-1) 0 0 (-1) 0 (by omega) (by omega) (by omega) s.inv hc.inl
      (dgComp 1 (-1) 0 (by omega) hc.fst s.hom),
    ← dgComp_assoc (-1) 1 (-1) 0 0 (-1) (by omega) (by omega) (by omega) hc.inl hc.fst s.hom,
    hc.inl_comp_fst, dgId_comp, s.inv_hom]

/-- The connecting morphism absorbs the shift out of `rotateBwd`'s
`inl_W`-component: `s.hom ≫ s.inv = dgId`. -/
lemma rotateFwd_absorb_inl :
    dgComp 0 1 1 (by omega) (hc.toShift s) (dgComp 1 0 1 (by omega) s.inv f) =
      dgComp 1 0 1 (by omega) hc.fst f := by
  rw [toShift,
    dgComp_assoc 1 (-1) 1 0 0 1 (by omega) (by omega) (by omega) hc.fst s.hom
      (dgComp 1 0 1 (by omega) s.inv f),
    ← dgComp_assoc (-1) 1 0 0 1 0 (by omega) (by omega) (by omega) s.hom s.inv f,
    s.hom_inv, dgId_comp]

/-- And out of its `inr_W`-component. -/
lemma rotateFwd_absorb_inr :
    dgComp 0 0 0 (by omega) (hc.toShift s) (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) =
      dgComp 1 (-1) 0 (by omega) hc.fst hc.inl := by
  rw [toShift,
    dgComp_assoc 1 (-1) 0 0 (-1) 0 (by omega) (by omega) (by omega) hc.fst s.hom
      (dgComp 1 (-1) 0 (by omega) s.inv hc.inl),
    ← dgComp_assoc (-1) 1 (-1) 0 0 (-1) (by omega) (by omega) (by omega) s.hom s.inv hc.inl,
    s.hom_inv, dgId_comp]

/-- The homotopy's core computation. `snd_W ≫ snd` is not closed, and its
differential is exactly the `inl_W`-coefficient the composite has to correct:
both cones contribute their own failure, and `inr ≫ snd = dgId` turns the second
contribution into `fst_W` on the nose. -/
lemma delta_sndComp :
    ((dgHom W Y).d 0 1).hom (dgComp 0 0 0 (by omega) hd.snd hc.snd) =
      -dgComp 0 1 1 (by omega) hd.snd (dgComp 1 0 1 (by omega) hc.fst f) - hd.fst := by
  have hleib : ((dgHom W Y).d 0 1).hom (dgComp 0 0 0 (by omega) hd.snd hc.snd) =
      dgComp 0 1 1 (by omega) hd.snd (((dgHom Z Y).d 0 1).hom hc.snd) +
        (0 : ℤ).negOnePow •
          dgComp 1 0 1 (by omega) (((dgHom W Z).d 0 1).hom hd.snd) hc.snd :=
    dgComp_leibniz (X := W) (Y := Z) (Z := Y) 0 0 0 1 (by omega) (by omega) hd.snd hc.snd
  rw [hleib, hc.delta_snd, hd.delta_snd, Int.negOnePow_zero, one_smul]
  simp only [map_neg, AddMonoidHom.neg_apply]
  rw [dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega) hd.fst hc.inr hc.snd,
    hc.inr_comp_snd, dgComp_id]
  abel

/-- The composite in the other order, split along the cone's two inclusions. -/
lemma rotateFwd_comp_rotateBwd_eq :
    dgComp 0 0 0 (by omega) (hc.rotateFwd hd s) (hc.rotateBwd hd s) =
      dgComp 1 (-1) 0 (by omega)
          (-dgComp 0 1 1 (by omega) hd.snd (dgComp 1 0 1 (by omega) hc.fst f)) hd.inl +
        dgComp 0 0 0 (by omega)
          (dgComp 0 0 0 (by omega) hd.snd (dgComp 1 (-1) 0 (by omega) hc.fst hc.inl))
          hd.inr := by
  rw [rotateBwd, rotateFwd, map_add]
  congr 1
  · rw [dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) hd.snd (hc.toShift s)
        (dgComp 1 (-1) 0 (by omega) (-dgComp 1 0 1 (by omega) s.inv f) hd.inl),
      ← dgComp_assoc 0 1 (-1) 1 0 0 (by omega) (by omega) (by omega) (hc.toShift s)
        (-dgComp 1 0 1 (by omega) s.inv f) hd.inl]
    simp only [map_neg, AddMonoidHom.neg_apply]
    rw [hc.rotateFwd_absorb_inl s, ← dgComp_assoc 0 1 (-1) 1 0 0 (by omega) (by omega)
        (by omega) hd.snd (dgComp 1 0 1 (by omega) hc.fst f) hd.inl]
  · rw [dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) hd.snd (hc.toShift s)
        (dgComp 0 0 0 (by omega) (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) hd.inr),
      ← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) (hc.toShift s)
        (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) hd.inr,
      hc.rotateFwd_absorb_inr s,
      ← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) hd.snd
        (dgComp 1 (-1) 0 (by omega) hc.fst hc.inl) hd.inr]

/-- **The other composite is the identity up to homotopy.** The primitive is
`-(snd_W ≫ snd) ≫ inl_W`, and `delta_sndComp` is why: its differential is the
`inl_W`-coefficient the composite has to correct, while the `inr_W`-coefficient
is corrected by the original cone's splitting of `dgId`. -/
lemma rotateFwd_comp_rotateBwd_sub_dgId :
    dgComp 0 0 0 (by omega) (hc.rotateFwd hd s) (hc.rotateBwd hd s) - dgId W ∈
      coboundaries W W := by
  refine ⟨dgComp 0 (-1) (-1) (by omega)
    (-dgComp 0 0 0 (by omega) hd.snd hc.snd) hd.inl, ?_⟩
  have hleib : ((dgHom W W).d (-1) 0).hom
        (dgComp 0 (-1) (-1) (by omega)
          (-dgComp 0 0 0 (by omega) hd.snd hc.snd) hd.inl) =
      dgComp 0 0 0 (by omega) (-dgComp 0 0 0 (by omega) hd.snd hc.snd)
          (((dgHom Y W).d (-1) 0).hom hd.inl) +
        (-1 : ℤ).negOnePow • dgComp 1 (-1) 0 (by omega)
          (((dgHom W Y).d 0 1).hom (-dgComp 0 0 0 (by omega) hd.snd hc.snd)) hd.inl :=
    dgComp_leibniz (X := W) (Y := Y) (Z := W) 0 (-1) (-1) 0 (by omega) (by omega) _ hd.inl
  have hneg : (-1 : ℤ).negOnePow = -1 := by decide
  rw [hleib, hd.δ_inl, hneg]
  simp only [map_neg, AddMonoidHom.neg_apply, Units.neg_smul, one_smul, neg_neg]
  rw [hc.delta_sndComp hd, hc.rotateFwd_comp_rotateBwd_eq hd s]
  simp only [map_sub, AddMonoidHom.sub_apply, map_neg, AddMonoidHom.neg_apply]
  rw [← hd.fst_inl_add_snd_inr]
  have key : dgComp 0 0 0 (by omega) (dgComp 0 0 0 (by omega) hd.snd hc.snd)
        (dgComp 0 0 0 (by omega) hc.inr hd.inr) +
      dgComp 0 0 0 (by omega)
        (dgComp 0 0 0 (by omega) hd.snd (dgComp 1 (-1) 0 (by omega) hc.fst hc.inl))
        hd.inr =
      dgComp 0 0 0 (by omega) hd.snd hd.inr := by
    rw [← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega)
        (dgComp 0 0 0 (by omega) hd.snd hc.snd) hc.inr hd.inr,
      dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) hd.snd hc.snd hc.inr,
      ← AddMonoidHom.add_apply, ← map_add, ← map_add, add_comm
        (dgComp 0 0 0 (by omega) hc.snd hc.inr), hc.fst_inl_add_snd_inr, dgComp_id]
  rw [← key]
  abel

section TriangleMaps

variable {Y' : C} (s' : IsShiftBy Y 1 Y')

/-- **The rotated triangle's third map, on the nose.** `rotateBwd` followed by the
cone-on-`inr`'s connecting morphism is `-f⟦1⟧`, with no homotopy: the
`inr_W`-component dies against `fst_W`, the `inl_W`-component survives through
`inl_W ≫ fst_W = dgId`, and what is left is literally `mapShift`'s definition.

This is the third commuting square of the rotation isomorphism, and that it holds
strictly is why the sign of `rotateBwd` had to be what it is. -/
lemma rotateBwd_comp_toShift :
    dgComp 0 0 0 (by omega) (hc.rotateBwd hd s) (hd.toShift s') =
      -IsShiftBy.mapShift s s' f := by
  rw [rotateBwd, toShift, map_add, AddMonoidHom.add_apply,
    dgComp_assoc 1 (-1) 0 0 (-1) 0 (by omega) (by omega) (by omega)
      (-dgComp 1 0 1 (by omega) s.inv f) hd.inl (dgComp 1 (-1) 0 (by omega) hd.fst s'.hom),
    dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega)
      (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) hd.inr
      (dgComp 1 (-1) 0 (by omega) hd.fst s'.hom),
    ← dgComp_assoc (-1) 1 (-1) 0 0 (-1) (by omega) (by omega) (by omega) hd.inl hd.fst s'.hom,
    ← dgComp_assoc 0 1 (-1) 1 0 0 (by omega) (by omega) (by omega) hd.inr hd.fst s'.hom,
    hd.inl_comp_fst, hd.inr_comp_fst, dgId_comp]
  simp only [map_zero, AddMonoidHom.zero_apply, map_neg, AddMonoidHom.neg_apply, add_zero]
  rw [IsShiftBy.mapShift, dgComp_assoc 1 0 (-1) 1 (-1) 0 (by omega) (by omega) (by omega)]

/-- The rotated triangle's second map, split along the cone's two inclusions. -/
lemma toShift_comp_rotateBwd_eq :
    dgComp 0 0 0 (by omega) (hc.toShift s) (hc.rotateBwd hd s) =
      dgComp 1 (-1) 0 (by omega) (-dgComp 1 0 1 (by omega) hc.fst f) hd.inl +
        dgComp 0 0 0 (by omega) (dgComp 1 (-1) 0 (by omega) hc.fst hc.inl) hd.inr := by
  rw [rotateBwd, map_add,
    ← dgComp_assoc 0 1 (-1) 1 0 0 (by omega) (by omega) (by omega) (hc.toShift s)
      (-dgComp 1 0 1 (by omega) s.inv f) hd.inl,
    ← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) (hc.toShift s)
      (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) hd.inr]
  simp only [map_neg, AddMonoidHom.neg_apply]
  rw [hc.rotateFwd_absorb_inl s, hc.rotateFwd_absorb_inr s]

/-- **The rotated triangle's second square, up to homotopy.** The primitive is
`-(snd ≫ inl_W)`: its differential supplies the `inl_W`-coefficient through the
original cone's `δ snd = -(fst ≫ f)`, and the `inr_W`-coefficient through the
cone's splitting of `dgId Z`. -/
lemma toShift_comp_rotateBwd_sub_inr :
    dgComp 0 0 0 (by omega) (hc.toShift s) (hc.rotateBwd hd s) - hd.inr ∈
      coboundaries Z W := by
  refine ⟨-dgComp 0 (-1) (-1) (by omega) hc.snd hd.inl, ?_⟩
  have hleib : ((dgHom Z W).d (-1) 0).hom (dgComp 0 (-1) (-1) (by omega) hc.snd hd.inl) =
      dgComp 0 0 0 (by omega) hc.snd (((dgHom Y W).d (-1) 0).hom hd.inl) +
        (-1 : ℤ).negOnePow • dgComp 1 (-1) 0 (by omega)
          (((dgHom Z Y).d 0 1).hom hc.snd) hd.inl :=
    dgComp_leibniz (X := Z) (Y := Y) (Z := W) 0 (-1) (-1) 0 (by omega) (by omega)
      hc.snd hd.inl
  have hneg : (-1 : ℤ).negOnePow = -1 := by decide
  rw [map_neg, hleib, hd.δ_inl, hneg, hc.delta_snd]
  simp only [map_neg, AddMonoidHom.neg_apply, Units.neg_smul, one_smul, neg_neg, neg_add]
  rw [hc.toShift_comp_rotateBwd_eq hd s]
  -- Stated with the *composite* on the left, not `hd.inr`: that term occurs exactly
  -- once in the goal, so the rewrite has no other place to fire.
  have key : dgComp 0 0 0 (by omega) (dgComp 1 (-1) 0 (by omega) hc.fst hc.inl) hd.inr =
      hd.inr - dgComp 0 0 0 (by omega) hc.snd (dgComp 0 0 0 (by omega) hc.inr hd.inr) := by
    refine eq_sub_of_add_eq ?_
    rw [← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) hc.snd hc.inr hd.inr,
      ← AddMonoidHom.add_apply, ← map_add, hc.fst_inl_add_snd_inr, dgId_comp]
  rw [key]
  simp only [neg_smul, one_smul, map_neg, AddMonoidHom.neg_apply]
  abel

end TriangleMaps

end Composites

end IsConeOf

end CategoryTheory
