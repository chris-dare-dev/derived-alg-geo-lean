/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.NaturalTransformationH0

/-!
# `H⁰` of the dg category of dg functors, compared with ordinary functors

`DGFunctor C D` is itself a dg category, so `H⁰ (DGFunctor C D)` is an ordinary
category: its objects are dg functors and its morphisms are closed degree-zero
dg natural transformations up to homotopy.  Separately, every dg functor has an
`H⁰` and every closed degree-zero transformation descends to one.  This file
says those two facts assemble into a functor

`H⁰ (DGFunctor C D) ⥤ (H⁰ C ⥤ H⁰ D)`.

## What the functor is, and what it is not

It is the comparison map, and it is the reason the dg functor category is worth
having: without it, `DGFunctor C D` and `H⁰ C ⥤ H⁰ D` are two unrelated
categories that happen to have related objects.

It is **not** claimed to be full, faithful, or essentially surjective, and none
of the three is true in general.  An ordinary natural transformation between
the induced functors need not lift to a dg one, two dg transformations can
descend to the same ordinary one without being homotopic in any recorded sense
beyond the quotient's own, and an arbitrary functor `H⁰ C ⥤ H⁰ D` need not come
from a dg functor at all.  Making any of those precise is the Morita and
quasi-functor theory the roadmap lists as open.

## Homotopy invariance is the only content

Everything else is bookkeeping.  The one step that has to be checked is that a
morphism of `H⁰ (DGFunctor C D)` — a homotopy class — determines the induced
ordinary transformation.  It does, componentwise: if `α - β = δ θ` in the dg
functor category then `α X - β X = δ (θ X)` in `D`, because the differential of
the dg functor category is the pointwise one, so the two components agree in
`H⁰ D`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]

/-- A degree-zero cocycle of the dg category of dg functors is a closed
homogeneous natural transformation.  The two say the same thing: the
differential of `DGFunctor C D` is the pointwise one by definition. -/
theorem isClosed_of_mem_cocycles {F G : DGFunctor C D}
    {η : HomogeneousNatTrans F G 0} (hη : η ∈ cocycles F G) :
    HomogeneousNatTrans.IsClosed η :=
  (HomogeneousNatTrans.complex_d_apply η).symm.trans hη

/-- Conversely, a closed transformation is a cocycle. -/
theorem mem_cocycles_of_isClosed {F G : DGFunctor C D}
    {η : HomogeneousNatTrans F G 0} (hη : HomogeneousNatTrans.IsClosed η) :
    η ∈ cocycles F G :=
  (HomogeneousNatTrans.complex_d_apply η).trans hη

/-- Descending a vertical composite is composing the descents. -/
theorem HomogeneousNatTrans.h0_comp {F G H : DGFunctor C D}
    (η : HomogeneousNatTrans F G 0) (θ : HomogeneousNatTrans G H 0)
    (hη : HomogeneousNatTrans.IsClosed η)
    (hθ : HomogeneousNatTrans.IsClosed θ)
    (hηθ : HomogeneousNatTrans.IsClosed
      (HomogeneousNatTrans.composition F G H 0 0 0 (by omega) η θ)) :
    HomogeneousNatTrans.h0 _ hηθ =
      HomogeneousNatTrans.h0 η hη ≫ HomogeneousNatTrans.h0 θ hθ := by
  ext X
  rw [HomogeneousNatTrans.h0_app]
  show _ = H0.homMk (C := D) _ ≫ H0.homMk (C := D) _
  rw [H0.homMk_comp]
  exact congrArg _ (Subtype.ext
    (HomogeneousNatTrans.composition_apply_app η θ 0 (by omega) (H0.of C X)))

variable (C D) in
/-- **The comparison functor.**

An object of `H⁰ (DGFunctor C D)` is a dg functor, and it goes to the induced
functor on `H⁰`.  A morphism is a homotopy class of closed degree-zero dg
natural transformations, and it goes to the ordinary transformation any
representative descends to. -/
noncomputable def h0Comparison : H0 (DGFunctor C D) ⥤ (H0 C ⥤ H0 D) where
  obj F := (H0.of (DGFunctor C D) F).h0
  map {F G} η :=
    Quotient.liftOn η
      (fun a => HomogeneousNatTrans.h0 a.1 (isClosed_of_mem_cocycles a.2))
      (by
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hr
        have hab := QuotientAddGroup.leftRel_apply.mp hr
        simp only [H0.coboundariesIn, AddSubgroup.mem_addSubgroupOf] at hab
        obtain ⟨θ, hθ⟩ := hab
        -- The differential of the dg functor category is the pointwise one.
        -- `complex_d_apply` is stated at `n` and `n + 1`; the index here is
        -- `-1` and `0`, which are equal only definitionally, so it is applied
        -- as a term rather than rewritten with.
        have hdiff : ((dgHom (H0.of (DGFunctor C D) F)
              (H0.of (DGFunctor C D) G)).d (-1) 0).hom θ =
            HomogeneousNatTrans.differential θ :=
          HomogeneousNatTrans.complex_d_apply θ
        rw [hdiff] at hθ
        ext X
        rw [HomogeneousNatTrans.h0_app, HomogeneousNatTrans.h0_app]
        refine H0.homMk_eq_homMk ?_
        -- `-a + b = δ θ` in the dg functor category, so componentwise
        -- `a X - b X = δ (-θ X)` in `D`.
        refine ⟨-HomogeneousNatTrans.app θ (H0.of C X), ?_⟩
        -- Ascribed rather than rewritten, for the same index reason: the
        -- component of a differential is `differential_app`, which is stated
        -- at `n` and `n + 1`.
        have hc : ((dgHom ((H0.of (DGFunctor C D) F).obj (H0.of C X))
              ((H0.of (DGFunctor C D) G).obj (H0.of C X))).d (-1) 0).hom
              (HomogeneousNatTrans.app θ (H0.of C X)) =
            HomogeneousNatTrans.app (-a + b) (H0.of C X) :=
          congrArg (fun σ => HomogeneousNatTrans.app σ (H0.of C X)) hθ
        rw [map_neg, hc]
        show -(HomogeneousNatTrans.app (-a + b) (H0.of C X)) =
          HomogeneousNatTrans.app a (H0.of C X) -
            HomogeneousNatTrans.app b (H0.of C X)
        rw [HomogeneousNatTrans.add_app, HomogeneousNatTrans.neg_app]
        abel)
  map_id F := by
    show HomogeneousNatTrans.h0 _ _ = _
    exact HomogeneousNatTrans.h0_id _ _
  map_comp {F G H} η θ := by
    induction η using Quotient.ind with
    | _ η =>
      induction θ using Quotient.ind with
      | _ θ =>
        exact HomogeneousNatTrans.h0_comp η.1 θ.1
          (isClosed_of_mem_cocycles η.2) (isClosed_of_mem_cocycles θ.2) _

@[simp]
theorem h0Comparison_obj (F : H0 (DGFunctor C D)) :
    (h0Comparison C D).obj F = (H0.of (DGFunctor C D) F).h0 :=
  rfl

@[simp]
theorem h0Comparison_map_mk {F G : H0 (DGFunctor C D)}
    (a : cocycles (H0.of (DGFunctor C D) F) (H0.of (DGFunctor C D) G)) :
    (h0Comparison C D).map (QuotientAddGroup.mk a) =
      HomogeneousNatTrans.h0 a.1 (isClosed_of_mem_cocycles a.2) :=
  rfl

/-- An isomorphism of dg functors in the closed degree-zero category descends
to a natural isomorphism between their `H⁰` functors.  This is the image under
the canonical composite `Z⁰ → H⁰ → Fun(H⁰ C, H⁰ D)`. -/
noncomputable def h0Iso {F G : Z0 (DGFunctor C D)} (e : F ≅ G) :
    (Z0.of (DGFunctor C D) F).h0 ≅ (Z0.of (DGFunctor C D) G).h0 :=
  (h0Comparison C D).mapIso ((Z0.toH0 (DGFunctor C D)).mapIso e)

@[simp]
theorem h0Iso_hom {F G : Z0 (DGFunctor C D)} (e : F ≅ G) :
    (h0Iso e).hom =
      HomogeneousNatTrans.h0 e.hom.val
        (isClosed_of_mem_cocycles e.hom.2) :=
  rfl

@[simp]
theorem h0Iso_inv {F G : Z0 (DGFunctor C D)} (e : F ≅ G) :
    (h0Iso e).inv =
      HomogeneousNatTrans.h0 e.inv.val
        (isClosed_of_mem_cocycles e.inv.2) :=
  rfl

@[simp]
theorem h0Iso_hom_app {F G : Z0 (DGFunctor C D)} (e : F ≅ G) (X : H0 C) :
    ((h0Iso e).app X).hom =
      (HomogeneousNatTrans.h0 e.hom.val
        (isClosed_of_mem_cocycles e.hom.2)).app X :=
  rfl

@[simp]
theorem h0Iso_inv_app {F G : Z0 (DGFunctor C D)} (e : F ≅ G) (X : H0 C) :
    ((h0Iso e).app X).inv =
      (HomogeneousNatTrans.h0 e.inv.val
        (isClosed_of_mem_cocycles e.inv.2)).app X :=
  rfl

@[simp]
theorem h0Iso_refl (F : Z0 (DGFunctor C D)) :
    h0Iso (Iso.refl F) = Iso.refl (Z0.of (DGFunctor C D) F).h0 := by
  calc
    h0Iso (Iso.refl F) =
        (h0Comparison C D).mapIso
          (Iso.refl ((Z0.toH0 (DGFunctor C D)).obj F)) := by
      rw [h0Iso, Functor.mapIso_refl]
      rfl
    _ = Iso.refl ((h0Comparison C D).obj
        ((Z0.toH0 (DGFunctor C D)).obj F)) :=
      Functor.mapIso_refl _ _
    _ = _ := rfl

theorem h0Iso_trans {F G H : Z0 (DGFunctor C D)} (e : F ≅ G) (f : G ≅ H) :
    h0Iso (e.trans f) = (h0Iso e).trans (h0Iso f) := by
  calc
    h0Iso (e.trans f) = (h0Comparison C D).mapIso
        (((Z0.toH0 (DGFunctor C D)).mapIso e).trans
          ((Z0.toH0 (DGFunctor C D)).mapIso f)) := by
      rw [h0Iso, Functor.mapIso_trans]
      rfl
    _ = ((h0Comparison C D).mapIso
          ((Z0.toH0 (DGFunctor C D)).mapIso e)).trans
        ((h0Comparison C D).mapIso
          ((Z0.toH0 (DGFunctor C D)).mapIso f)) :=
      Functor.mapIso_trans _ _ _
    _ = _ := rfl

end DGFunctor

end CategoryTheory
