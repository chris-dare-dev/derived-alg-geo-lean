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

set_option backward.isDefEq.respectTransparency false in
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


end

end AlgebraicGeometry.Scheme.Modules
