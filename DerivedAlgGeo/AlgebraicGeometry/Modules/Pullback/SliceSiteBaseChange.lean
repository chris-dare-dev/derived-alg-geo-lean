/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Restriction
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.BaseChange

/-!
# The open-square comparison on slice-site module sheaves

The restriction of an ordinary pushforward to a slice agrees with the
pushforward on that slice. This comparison uses the independent open-square
pushforward isomorphism, transported through the two slice-site equivalences.
It is not a relative base-change isomorphism.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable section

/-- The independent open-square pushforward comparison, expressed on the slice
site. Its middle factor is `pushforwardRestrictNatIso`; the remaining factors
transport through `overEquiv` and `overFunctorEquiv`. -/
def pushforwardOverIso (f : X ⟶ Y) (M : X.Modules) (U : Y.Opens) :
    ((pushforward f).obj M).over U ≅
      (pushforwardOverFunctor f U).obj (M.over (f ⁻¹ᵁ U)) := by
  let V : X.Opens := f ⁻¹ᵁ U
  let A : U.toScheme.Modules :=
    (pushforward (f ∣_ U)).obj ((overEquiv V).functor.obj (M.over V))
  let e : (overEquiv U).functor.obj (((pushforward f).obj M).over U) ≅ A :=
    (overFunctorEquiv U).app ((pushforward f).obj M) ≪≫
      (AlgebraicGeometry.pushforwardRestrictNatIso f U).app M ≪≫
      (pushforward (f ∣_ U)).mapIso ((overFunctorEquiv V).app M).symm
  exact (overEquiv U).fullyFaithfulFunctor.preimageIso
    (e ≪≫ ((overEquiv U).counitIso.app A).symm)

/-- After applying the slice equivalence, `pushforwardOverIso` is the direct
open-square comparison, between the two restriction-equivalence factors. -/
theorem overEquiv_map_pushforwardOverIso_hom (f : X ⟶ Y) (M : X.Modules)
    (U : Y.Opens) :
    (overEquiv U).functor.map (pushforwardOverIso f M U).hom =
      (overFunctorEquiv U).hom.app ((pushforward f).obj M) ≫
        (AlgebraicGeometry.pushforwardRestrictNatIso f U).hom.app M ≫
        (pushforward (f ∣_ U)).map ((overFunctorEquiv (f ⁻¹ᵁ U)).inv.app M) ≫
        (overEquiv U).counitIso.inv.app
          ((pushforward (f ∣_ U)).obj
            ((overEquiv (f ⁻¹ᵁ U)).functor.obj (M.over (f ⁻¹ᵁ U)))) := by
  simp only [pushforwardOverIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  rfl

/-- The preexisting objectwise `pullbackOverIso` is the geometric pullback
comparison after transport through the slice equivalence. -/
theorem overEquiv_map_pullbackOverIso_hom (f : X ⟶ Y) (N : Y.Modules)
    (U : Y.Opens) :
    (overEquiv (f ⁻¹ᵁ U)).functor.map (pullbackOverIso f N U).hom =
      (overFunctorEquiv (f ⁻¹ᵁ U)).hom.app ((pullback f).obj N) ≫
        (AlgebraicGeometry.pullbackRestrictNatIso f U).hom.app N ≫
        (pullback (f ∣_ U)).map ((overFunctorEquiv U).inv.app N) ≫
        (overEquiv (f ⁻¹ᵁ U)).counitIso.inv.app
          ((pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (N.over U))) := by
  simp only [pullbackOverIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom,
    AlgebraicGeometry.pullbackRestrictNatIso, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_inv, Functor.map_comp, Category.assoc]
  rfl

-- The expanded composite-adjunction unit needs `instances` transparency at this
-- pinned Mathlib version; keep the relaxation scoped to this theorem.
set_option backward.isDefEq.respectTransparency false in
/-- Transporting the unit of the composite slice-site adjunction through the
outer equivalence gives the actual unit for the restricted scheme morphism,
followed by the inverse counit of the inner equivalence. -/
theorem overEquiv_map_pullbackOverAdjunction_unit (f : X ⟶ Y) (U : Y.Opens)
    (A : SheafOfModules (Y.ringCatSheaf.over U)) :
    (overEquiv U).functor.map ((pullbackOverAdjunction f U).unit.app A) ≫
      (overEquiv U).counitIso.hom.app
        ((pushforward (f ∣_ U)).obj
          ((overEquiv (f ⁻¹ᵁ U)).functor.obj
            ((overEquiv (f ⁻¹ᵁ U)).inverse.obj
              ((pullback (f ∣_ U)).obj ((overEquiv U).functor.obj A))))) =
    (pullbackPushforwardAdjunction (f ∣_ U)).unit.app ((overEquiv U).functor.obj A) ≫
      (pushforward (f ∣_ U)).map
        ((overEquiv (f ⁻¹ᵁ U)).counitIso.inv.app
          ((pullback (f ∣_ U)).obj ((overEquiv U).functor.obj A))) := by
  let e := overEquiv U
  let q := (pullbackPushforwardAdjunction (f ∣_ U)).unit.app (e.functor.obj A) ≫
    (pushforward (f ∣_ U)).map
      ((overEquiv (f ⁻¹ᵁ U)).counitIso.inv.app
        ((pullback (f ∣_ U)).obj (e.functor.obj A)))
  change e.functor.map (e.unit.app A ≫ e.inverse.map q) ≫ e.counit.app _ = q
  rw [Functor.map_comp, Category.assoc, e.counit_naturality q, ← Category.assoc]
  exact (congrArg (fun t => t ≫ q) (e.functor_unit_comp A)).trans (Category.id_comp q)

private theorem counitInv_map_counit {C : Type*} {D : Type*}
    [Category C] [Category D] (e : C ≌ D) {A B : D} (h : A ⟶ B) :
    e.counitInv.app A ≫ e.functor.map (e.inverse.map h) ≫ e.counit.app B = h := by
  have h₁ := congrArg (fun t => t ≫ e.counit.app B) (e.counitInv_naturality h)
  have h₂ := congrArg (fun t => h ≫ t) (e.counitIso.inv_hom_id_app B)
  exact (Category.assoc _ _ _).symm.trans
    (h₁.trans ((Category.assoc _ _ _).trans (h₂.trans (Category.comp_id h))))

/-- Mapping a slice-site morphism by pushforward agrees, under the outer
equivalence's counit, with mapping its transported morphism by the restricted
scheme pushforward. -/
theorem pushforwardOverFunctor_map_transport (f : X ⟶ Y) (U : Y.Opens)
    {A B : SheafOfModules (X.ringCatSheaf.over (f ⁻¹ᵁ U))} (g : A ⟶ B) :
    (overEquiv U).counitIso.inv.app
        ((pushforward (f ∣_ U)).obj ((overEquiv (f ⁻¹ᵁ U)).functor.obj A)) ≫
      (overEquiv U).functor.map ((pushforwardOverFunctor f U).map g) ≫
      (overEquiv U).counitIso.hom.app
        ((pushforward (f ∣_ U)).obj ((overEquiv (f ⁻¹ᵁ U)).functor.obj B)) =
    (pushforward (f ∣_ U)).map ((overEquiv (f ⁻¹ᵁ U)).functor.map g) := by
  let e := overEquiv U
  let h := (pushforward (f ∣_ U)).map ((overEquiv (f ⁻¹ᵁ U)).functor.map g)
  change e.counitInv.app _ ≫ e.functor.map (e.inverse.map h) ≫ e.counit.app _ = h
  exact counitInv_map_counit e h

-- The pinned sheaf-category instances need this relaxation when rewriting the
-- two transported morphisms; keep it local to the normal-form theorem.
set_option backward.isDefEq.respectTransparency false in
/-- The slice-site pushforward comparison followed by a slice morphism has
this direct open-square normal form after applying the outer equivalence and
its counit. This is not the slice-site unit square or a relative `IsIso`. -/
theorem pushforwardOverIso_map_normal_form (f : X ⟶ Y) (M : X.Modules)
    (U : Y.Opens)
    {B : SheafOfModules (X.ringCatSheaf.over (f ⁻¹ᵁ U))}
    (g : M.over (f ⁻¹ᵁ U) ⟶ B) :
    (overEquiv U).functor.map (pushforwardOverIso f M U).hom ≫
      (overEquiv U).functor.map ((pushforwardOverFunctor f U).map g) ≫
      (overEquiv U).counitIso.hom.app
        ((pushforward (f ∣_ U)).obj ((overEquiv (f ⁻¹ᵁ U)).functor.obj B)) =
    (overFunctorEquiv U).hom.app ((pushforward f).obj M) ≫
      (AlgebraicGeometry.pushforwardRestrictNatIso f U).hom.app M ≫
      (pushforward (f ∣_ U)).map
        ((overFunctorEquiv (f ⁻¹ᵁ U)).inv.app M ≫
          (overEquiv (f ⁻¹ᵁ U)).functor.map g) := by
  rw [overEquiv_map_pushforwardOverIso_hom]
  simp only [Category.assoc]
  rw [pushforwardOverFunctor_map_transport]
  rfl

-- The two geometric isomorphisms and the inner equivalence cancel before the
-- slice-site unit is compared.  Keeping this typed avoids unfolding the sheaf
-- categories in the final diagram chase.
private theorem cancel_two_isos {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (j : B ≅ D) (h : D ⟶ E) :
    j.inv ≫ i.inv ≫ i.hom ≫ j.hom ≫ h = h := by
  simp only [Iso.inv_hom_id_assoc]

private theorem adjunction_unit_iso_transport {C D : Type*}
    [Category C] [Category D] (L : C ⥤ D) (R : D ⥤ C)
    (a : L ⊣ R) {A B : C} (i : A ≅ B) {T : D} (h : L.obj A ⟶ T) :
    i.hom ≫ a.unit.app B ≫ R.map (L.map i.inv ≫ h) =
      a.unit.app A ≫ R.map h := by
  have hn : i.hom ≫ a.unit.app B =
      a.unit.app A ≫ R.map (L.map i.hom) := by
    exact a.unit.naturality i.hom
  have hi : L.map i.hom ≫ L.map i.inv = 𝟙 (L.obj A) :=
    (Functor.map_comp L i.hom i.inv).symm.trans
      ((congrArg L.map i.hom_inv_id).trans (L.map_id A))
  have hc : L.map i.hom ≫ (L.map i.inv ≫ h) = h :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ h) hi).trans (Category.id_comp h))
  calc
    _ = (i.hom ≫ a.unit.app B) ≫ R.map (L.map i.inv ≫ h) := by
      exact (Category.assoc _ _ _).symm
    _ = (a.unit.app A ≫ R.map (L.map i.hom)) ≫ R.map (L.map i.inv ≫ h) := by
      exact congrArg (fun t => t ≫ R.map (L.map i.inv ≫ h)) hn
    _ = a.unit.app A ≫ R.map (L.map i.hom ≫ (L.map i.inv ≫ h)) := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun t => a.unit.app A ≫ t) (Functor.map_comp R _ _).symm)
    _ = a.unit.app A ≫ R.map h := by
      exact congrArg (fun t => a.unit.app A ≫ R.map t) hc

private theorem pullbackOverIso_cancellation (f : X ⟶ Y) (N : Y.Modules)
    (U : Y.Opens) :
    (AlgebraicGeometry.pullbackRestrictNatIso f U).inv.app N ≫
      (overFunctorEquiv (f ⁻¹ᵁ U)).inv.app ((pullback f).obj N) ≫
      (overEquiv (f ⁻¹ᵁ U)).functor.map (pullbackOverIso f N U).hom =
    (pullback (f ∣_ U)).map ((overFunctorEquiv U).inv.app N) ≫
      (overEquiv (f ⁻¹ᵁ U)).counitIso.inv.app
        ((pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (N.over U))) := by
  rw [overEquiv_map_pullbackOverIso_hom]
  exact cancel_two_isos
    ((overFunctorEquiv (f ⁻¹ᵁ U)).app ((pullback f).obj N))
    ((AlgebraicGeometry.pullbackRestrictNatIso f U).app N)
    ((pullback (f ∣_ U)).map ((overFunctorEquiv U).inv.app N) ≫
      (overEquiv (f ⁻¹ᵁ U)).counitIso.inv.app
        ((pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (N.over U))))

set_option backward.isDefEq.respectTransparency false in
/-- The actual global pullback unit and the composite slice-site unit agree
after restriction and the independent open-square comparisons. -/
theorem pullbackOverIso_unit_app (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens) :
    (SheafOfModules.overFunctor Y.ringCatSheaf U).map
        ((pullbackPushforwardAdjunction f).unit.app N) ≫
      (pushforwardOverIso f ((pullback f).obj N) U).hom ≫
      (pushforwardOverFunctor f U).map (pullbackOverIso f N U).hom =
    (pullbackOverAdjunction f U).unit.app (N.over U) := by
  have htransport :
      (overFunctorEquiv U).hom.app N ≫
        (pullbackPushforwardAdjunction (f ∣_ U)).unit.app
          ((restrictFunctor U.ι).obj N) ≫
        (pushforward (f ∣_ U)).map
          ((AlgebraicGeometry.pullbackRestrictNatIso f U).inv.app N ≫
            (overFunctorEquiv (f ⁻¹ᵁ U)).inv.app ((pullback f).obj N) ≫
            (overEquiv (f ⁻¹ᵁ U)).functor.map (pullbackOverIso f N U).hom) =
      (pullbackPushforwardAdjunction (f ∣_ U)).unit.app
        ((overEquiv U).functor.obj (N.over U)) ≫
        (pushforward (f ∣_ U)).map
          ((overEquiv (f ⁻¹ᵁ U)).counitIso.inv.app
            ((pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (N.over U)))) := by
    calc
      _ = (overFunctorEquiv U).hom.app N ≫
            (pullbackPushforwardAdjunction (f ∣_ U)).unit.app
              ((restrictFunctor U.ι).obj N) ≫
            (pushforward (f ∣_ U)).map
              ((pullback (f ∣_ U)).map ((overFunctorEquiv U).inv.app N) ≫
                (overEquiv (f ⁻¹ᵁ U)).counitIso.inv.app
                  ((pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (N.over U)))) := by
          exact congrArg (fun t =>
            (overFunctorEquiv U).hom.app N ≫
              (pullbackPushforwardAdjunction (f ∣_ U)).unit.app
                ((restrictFunctor U.ι).obj N) ≫
              (pushforward (f ∣_ U)).map t)
            (pullbackOverIso_cancellation f N U)
      _ = _ := adjunction_unit_iso_transport
        (pullback (f ∣_ U)) (pushforward (f ∣_ U))
        (pullbackPushforwardAdjunction (f ∣_ U))
        ((overFunctorEquiv U).app N)
        ((overEquiv (f ⁻¹ᵁ U)).counitIso.inv.app
          ((pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (N.over U))))
  have hnat :
      (overEquiv U).functor.map
          ((SheafOfModules.overFunctor Y.ringCatSheaf U).map
            ((pullbackPushforwardAdjunction f).unit.app N)) ≫
        (overFunctorEquiv U).hom.app ((pushforward f).obj ((pullback f).obj N)) =
      (overFunctorEquiv U).hom.app N ≫
        (restrictFunctor U.ι).map ((pullbackPushforwardAdjunction f).unit.app N) := by
    exact (overFunctorEquiv U).hom.naturality
      ((pullbackPushforwardAdjunction f).unit.app N)
  let q := (overFunctorEquiv (f ⁻¹ᵁ U)).inv.app ((pullback f).obj N) ≫
    (overEquiv (f ⁻¹ᵁ U)).functor.map (pullbackOverIso f N U).hom
  have htail :
      (restrictFunctor U.ι).map ((pullbackPushforwardAdjunction f).unit.app N) ≫
        ((AlgebraicGeometry.pushforwardRestrictNatIso f U).hom.app
            ((pullback f).obj N) ≫ (pushforward (f ∣_ U)).map q) =
      (pullbackPushforwardAdjunction (f ∣_ U)).unit.app
          ((restrictFunctor U.ι).obj N) ≫
        (pushforward (f ∣_ U)).map
          ((AlgebraicGeometry.pullbackRestrictNatIso f U).inv.app N ≫ q) := by
    calc
      _ = ((restrictFunctor U.ι).map
            ((pullbackPushforwardAdjunction f).unit.app N) ≫
          (AlgebraicGeometry.pushforwardRestrictNatIso f U).hom.app
            ((pullback f).obj N)) ≫ (pushforward (f ∣_ U)).map q :=
          (Category.assoc _ _ _).symm
      _ = ((pullbackPushforwardAdjunction (f ∣_ U)).unit.app
            ((restrictFunctor U.ι).obj N) ≫
          (pushforward (f ∣_ U)).map
            ((AlgebraicGeometry.pullbackRestrictNatIso f U).inv.app N)) ≫
          (pushforward (f ∣_ U)).map q :=
          congrArg (fun t => t ≫ (pushforward (f ∣_ U)).map q)
            (AlgebraicGeometry.pullbackRestrictNatIso_unit_app f U N)
      _ = (pullbackPushforwardAdjunction (f ∣_ U)).unit.app
            ((restrictFunctor U.ι).obj N) ≫
          (pushforward (f ∣_ U)).map
            ((AlgebraicGeometry.pullbackRestrictNatIso f U).inv.app N ≫ q) :=
          (Category.assoc _ _ _).trans
            (congrArg (fun t =>
              (pullbackPushforwardAdjunction (f ∣_ U)).unit.app
                ((restrictFunctor U.ι).obj N) ≫ t)
              ((pushforward (f ∣_ U)).map_comp
                ((AlgebraicGeometry.pullbackRestrictNatIso f U).inv.app N) q).symm)
  apply (overEquiv U).functor.map_injective
  rw [← cancel_mono ((overEquiv U).counitIso.hom.app
    ((pushforward (f ∣_ U)).obj
      ((overEquiv (f ⁻¹ᵁ U)).functor.obj
        ((pullbackOverFunctor f U).obj (N.over U)))))]
  simp only [Functor.map_comp]
  calc
    _ = (overEquiv U).functor.map
          ((SheafOfModules.overFunctor Y.ringCatSheaf U).map
            ((pullbackPushforwardAdjunction f).unit.app N)) ≫
        ((overEquiv U).functor.map
            (pushforwardOverIso f ((pullback f).obj N) U).hom ≫
          (overEquiv U).functor.map
            ((pushforwardOverFunctor f U).map (pullbackOverIso f N U).hom) ≫
          (overEquiv U).counitIso.hom.app
            ((pushforward (f ∣_ U)).obj
              ((overEquiv (f ⁻¹ᵁ U)).functor.obj
                ((pullbackOverFunctor f U).obj (N.over U))))) := by
          simp only [Category.assoc]
    _ = (overEquiv U).functor.map
          ((SheafOfModules.overFunctor Y.ringCatSheaf U).map
            ((pullbackPushforwardAdjunction f).unit.app N)) ≫
        ((overFunctorEquiv U).hom.app ((pushforward f).obj ((pullback f).obj N)) ≫
          (AlgebraicGeometry.pushforwardRestrictNatIso f U).hom.app
            ((pullback f).obj N) ≫
          (pushforward (f ∣_ U)).map
            ((overFunctorEquiv (f ⁻¹ᵁ U)).inv.app ((pullback f).obj N) ≫
              (overEquiv (f ⁻¹ᵁ U)).functor.map (pullbackOverIso f N U).hom)) := by
          exact congrArg (fun t =>
            (overEquiv U).functor.map
              ((SheafOfModules.overFunctor Y.ringCatSheaf U).map
                ((pullbackPushforwardAdjunction f).unit.app N)) ≫ t)
            (pushforwardOverIso_map_normal_form f ((pullback f).obj N) U
              (pullbackOverIso f N U).hom)
    _ = (overFunctorEquiv U).hom.app N ≫
        ((restrictFunctor U.ι).map
            ((pullbackPushforwardAdjunction f).unit.app N) ≫
          (AlgebraicGeometry.pushforwardRestrictNatIso f U).hom.app
            ((pullback f).obj N) ≫
          (pushforward (f ∣_ U)).map
            ((overFunctorEquiv (f ⁻¹ᵁ U)).inv.app ((pullback f).obj N) ≫
              (overEquiv (f ⁻¹ᵁ U)).functor.map (pullbackOverIso f N U).hom)) := by
          let k := (AlgebraicGeometry.pushforwardRestrictNatIso f U).hom.app
              ((pullback f).obj N) ≫ (pushforward (f ∣_ U)).map q
          change (overEquiv U).functor.map
              ((SheafOfModules.overFunctor Y.ringCatSheaf U).map
                ((pullbackPushforwardAdjunction f).unit.app N)) ≫
                ((overFunctorEquiv U).hom.app
                  ((pushforward f).obj ((pullback f).obj N)) ≫ k) =
              (overFunctorEquiv U).hom.app N ≫
                ((restrictFunctor U.ι).map
                  ((pullbackPushforwardAdjunction f).unit.app N) ≫ k)
          exact (Category.assoc _ _ _).symm.trans
            ((congrArg (fun t => t ≫ k) hnat).trans (Category.assoc _ _ _))
    _ = (overFunctorEquiv U).hom.app N ≫
        ((pullbackPushforwardAdjunction (f ∣_ U)).unit.app
            ((restrictFunctor U.ι).obj N) ≫
          (pushforward (f ∣_ U)).map
            ((AlgebraicGeometry.pullbackRestrictNatIso f U).inv.app N ≫
              (overFunctorEquiv (f ⁻¹ᵁ U)).inv.app ((pullback f).obj N) ≫
              (overEquiv (f ⁻¹ᵁ U)).functor.map (pullbackOverIso f N U).hom)) := by
          exact congrArg (fun t => (overFunctorEquiv U).hom.app N ≫ t) htail
    _ = (pullbackPushforwardAdjunction (f ∣_ U)).unit.app
          ((overEquiv U).functor.obj (N.over U)) ≫
        (pushforward (f ∣_ U)).map
          ((overEquiv (f ⁻¹ᵁ U)).counitIso.inv.app
            ((pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (N.over U)))) :=
          htransport
    _ = (overEquiv U).functor.map
          ((pullbackOverAdjunction f U).unit.app (N.over U)) ≫
        (overEquiv U).counitIso.hom.app
          ((pushforward (f ∣_ U)).obj
            ((overEquiv (f ⁻¹ᵁ U)).functor.obj
              ((pullbackOverFunctor f U).obj (N.over U)))) := by
          exact (overEquiv_map_pullbackOverAdjunction_unit f U (N.over U)).symm

end

end AlgebraicGeometry.Scheme.Modules
