/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.Localization.FixedTargetArrow
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.AffineSpec
import DerivedAlgGeo.CategoryTheory.SubobjectEquivalence
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.CategoryTheory.Whiskering

/-!
# Fixed-target arrows for affine coherent localization

This file transfers the fixed-target module arrow theorem to coherent sheaves on affine
noetherian schemes. It concerns ordinary coherent pullback, not derived pullback, a
bounded component, or an arbitrary t-heart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Functor
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry.Coh

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

private abbrev ringMap : CommRingCat.of R ⟶ CommRingCat.of A :=
  CommRingCat.ofHom (algebraMap R A)

private noncomputable def finiteExtendScalars : FGModuleCat.{u} R ⥤ FGModuleCat.{u} A :=
  (ModuleCat.isFG A).lift
    ((ModuleCat.isFG R).ι ⋙ ModuleCat.extendScalars (algebraMap R A))
    (fun M => by
      letI : Module.Finite R M.obj := M.property
      letI : Algebra R A := (algebraMap R A).toAlgebra
      change Module.Finite A
        ((ModuleCat.extendScalars (algebraMap R A)).obj M.obj)
      exact Module.Finite.base_change R A M.obj)

private noncomputable def affineTildePullbackCompιIso [IsNoetherianRing R]
    [IsNoetherianRing A] :
    (FGModuleCat.affineTilde (R := CommRingCat.of R) ⋙
        Coh.pullback (Spec.map (ringMap (R := R) (A := A)))) ⋙
        Coh.ι (Spec (CommRingCat.of A)) ≅
      (finiteExtendScalars (R := R) (A := A) ⋙
        FGModuleCat.affineTilde (R := CommRingCat.of A)) ⋙
        Coh.ι (Spec (CommRingCat.of A)) := by
  change (ModuleCat.isFG R).ι ⋙
      (AlgebraicGeometry.tilde.functor (CommRingCat.of R) ⋙
        Scheme.Modules.pullback (Spec.map (ringMap (R := R) (A := A)))) ≅
    (ModuleCat.isFG R).ι ⋙
      (ModuleCat.extendScalars (algebraMap R A) ⋙
        AlgebraicGeometry.tilde.functor (CommRingCat.of A))
  exact isoWhiskerLeft (ModuleCat.isFG R).ι
    (Scheme.Modules.pullbackSpecMapTildeIso (ringMap (R := R) (A := A)))

/-- The affine tilde/pullback square restricted to coherent sheaves. -/
private noncomputable def affineTildePullbackIso [IsNoetherianRing R]
    [IsNoetherianRing A] :
    FGModuleCat.affineTilde (R := CommRingCat.of R) ⋙
        Coh.pullback (Spec.map (ringMap (R := R) (A := A))) ≅
      finiteExtendScalars (R := R) (A := A) ⋙
        FGModuleCat.affineTilde (R := CommRingCat.of A) :=
  Functor.fullyFaithfulCancelRight (Coh.ι (Spec (CommRingCat.of A)))
    (affineTildePullbackCompιIso (R := R) (A := A))

private theorem finiteExtendScalars_fixedTargetArrow [IsNoetherianRing R]
    (S : Submonoid R) [IsLocalization S A] (M : FGModuleCat.{u} R) :
    Subobject.FixedTargetArrowExtension
      (finiteExtendScalars (R := R) (A := A)) M := by
  intro N β
  letI : Module R N := Module.compHom N (algebraMap R A)
  letI : Module.Finite R M := M.property
  letI : Module.Finite A N := N.property
  let alg : Algebra R A := inferInstance
  let hLoc : @IsLocalization R _ S A _ alg := inferInstance
  have hAlgEq : (algebraMap R A).toAlgebra = alg :=
    toAlgebra_algebraMap
  letI : Algebra R A := (algebraMap R A).toAlgebra
  haveI : IsLocalization S A := by
    exact (congrArg (fun a : Algebra R A => @IsLocalization R _ S A _ a)
      hAlgEq).mpr hLoc
  letI : IsScalarTower R A N := IsScalarTower.of_compHom R A N
  obtain ⟨L, hfp, f, e, hβ⟩ :=
    Module.exists_finitely_presented_fixedTargetArrow_of_isLocalization
      (R := R) (A := A) (N := N) (T := M) S β.hom.hom
  letI : Module.FinitePresentation R L := hfp
  let Y : FGModuleCat.{u} R := FGModuleCat.of R L
  let g : Y ⟶ M := ConcreteCategory.ofHom f
  let eCat : N ≅ (finiteExtendScalars (R := R) (A := A)).obj Y :=
    { hom := ConcreteCategory.ofHom e.toLinearMap
      inv := ConcreteCategory.ofHom e.symm.toLinearMap
      hom_inv_id := by ext x; exact e.left_inv x
      inv_hom_id := by ext x; exact e.right_inv x }
  have hmap :
      (IsLocalizedModule.mapExtendScalars S
        (TensorProduct.mk R A L 1) (TensorProduct.mk R A M 1) A) f =
        ((ModuleCat.extendScalars (algebraMap R A)).map
          (ModuleCat.ofHom f)).hom := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a l =>
      have ht : a ⊗ₜ[R] l = a • ((1 : A) ⊗ₜ[R] l) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, _root_.map_smul, _root_.map_smul]
      congr 1
      change ((IsLocalizedModule.mapExtendScalars S
          (TensorProduct.mk R A L 1) (TensorProduct.mk R A M 1) A) f)
          ((TensorProduct.mk R A L 1) l) =
        ((ModuleCat.extendScalars (algebraMap R A)).map
          (ModuleCat.ofHom f)).hom ((TensorProduct.mk R A L 1) l)
      rw [IsLocalizedModule.mapExtendScalars_apply_apply,
        IsLocalizedModule.map_apply]
      rfl
    | add x y hx hy =>
      simpa only [IsLocalizedModule.mapExtendScalars_apply_apply, _root_.map_add]
        using congrArg₂ HAdd.hAdd hx hy
  refine ⟨Y, g, eCat, ?_⟩
  apply FGModuleCat.hom_ext
  change β.hom.hom =
    (((ModuleCat.extendScalars (algebraMap R A)).map (ModuleCat.ofHom f)).hom).comp
      e.toLinearMap
  rw [← hmap]
  exact hβ

/-- Fixed-target arrow extension for coherent sheaves on an affine noetherian localization.
The target sheaf remains fixed; only the arrow's domain is replaced by an isomorphic pullback.
This is an underived statement about `Coh.pullback`. -/
theorem fixedTargetArrowExtension_pullbackSpecMap_of_isLocalization
    [IsNoetherianRing R] (S : Submonoid R) [IsLocalization S A]
    (E : Coh (Spec (CommRingCat.of R))) :
    Subobject.FixedTargetArrowExtension
      (Coh.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))) E := by
  letI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
  let ER := Coh.affineEquivalence (R := CommRingCat.of R)
  let EA := Coh.affineEquivalence (R := CommRingCat.of A)
  let FR := FGModuleCat.affineTilde (R := CommRingCat.of R)
  let FA := FGModuleCat.affineTilde (R := CommRingCat.of A)
  let F := Coh.pullback (Spec.map (ringMap (R := R) (A := A)))
  let G := finiteExtendScalars (R := R) (A := A)
  let α := affineTildePullbackIso (R := R) (A := A)
  intro Z β
  let M : FGModuleCat.{u} R := ER.functor.obj E
  let N : FGModuleCat.{u} A := EA.functor.obj Z
  let cR : E ≅ FR.obj M := ER.unitIso.app E
  let cA : Z ≅ FA.obj N := EA.unitIso.app Z
  letI : FA.Full := EA.fullyFaithfulInverse.full
  let βG : N ⟶ G.obj M :=
    FA.preimage (cA.inv ≫ β ≫ F.map cR.hom ≫ (α.app M).hom)
  obtain ⟨Y, g, e, hβG⟩ := finiteExtendScalars_fixedTargetArrow
    (R := R) (A := A) S M βG
  let L : Coh (Spec (CommRingCat.of R)) := FR.obj Y
  let fCoh : L ⟶ E := FR.map g ≫ cR.inv
  let eCoh : Z ≅ F.obj L :=
    cA ≪≫ FA.mapIso e ≪≫ (α.app Y).symm
  refine ⟨L, fCoh, eCoh, ?_⟩
  have hα : FA.map (G.map g) ≫ (α.app M).inv =
      (α.app Y).inv ≫ F.map (FR.map g) := by
    convert α.inv.naturality g using 1; rfl
  have hβFA : FA.map βG =
      cA.inv ≫ β ≫ F.map cR.hom ≫ (α.app M).hom := by
    exact FA.map_preimage _
  have hβGFA : FA.map βG = FA.map e.hom ≫ FA.map (G.map g) := by
    rw [hβG, Functor.map_comp]
  symm
  change eCoh.hom ≫ F.map fCoh = β
  calc
    eCoh.hom ≫ F.map fCoh =
        cA.hom ≫ FA.map e.hom ≫ (α.app Y).inv ≫
          F.map (FR.map g) ≫ F.map cR.inv := by
      simp only [eCoh, fCoh, Iso.trans_hom, Functor.map_comp,
        Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
      rfl
    _ = cA.hom ≫ FA.map e.hom ≫
          ((α.app Y).inv ≫ F.map (FR.map g)) ≫ F.map cR.inv := by
      simp only [Category.assoc]
    _ = cA.hom ≫ FA.map e.hom ≫
          (FA.map (G.map g) ≫ (α.app M).inv) ≫ F.map cR.inv := by
      exact congrArg
        (fun t => cA.hom ≫ FA.map e.hom ≫ t ≫ F.map cR.inv) hα.symm
    _ = cA.hom ≫ (FA.map e.hom ≫ FA.map (G.map g)) ≫
          (α.app M).inv ≫ F.map cR.inv := by
      simp only [Category.assoc]
    _ = cA.hom ≫ FA.map βG ≫ (α.app M).inv ≫ F.map cR.inv := by
      exact congrArg
        (fun t => cA.hom ≫ t ≫ (α.app M).inv ≫ F.map cR.inv) hβGFA.symm
    _ = cA.hom ≫ cA.inv ≫ β ≫ F.map cR.hom ≫
          (α.app M).hom ≫ (α.app M).inv ≫ F.map cR.inv := by
      rw [hβFA]
      cat_disch
    _ = cA.hom ≫ cA.inv ≫ β ≫ F.map cR.hom ≫
          ((α.app M).hom ≫ (α.app M).inv) ≫ F.map cR.inv := by
      simp only [Category.assoc]
    _ = cA.hom ≫ cA.inv ≫ β ≫ F.map cR.hom ≫
          (𝟙 (F.obj (FR.obj M))) ≫ F.map cR.inv := by
      exact congrArg
        (fun t => cA.hom ≫ cA.inv ≫ β ≫ F.map cR.hom ≫ t ≫ F.map cR.inv)
        (α.app M).hom_inv_id
    _ = cA.hom ≫ cA.inv ≫ β ≫ F.map cR.hom ≫ F.map cR.inv := by
      cat_disch
    _ = cA.hom ≫ cA.inv ≫ β := by
      simp only [← F.map_comp, cR.hom_inv_id, F.map_id]
      cat_disch
    _ = β := by
      simp only [Iso.hom_inv_id_assoc]

end AlgebraicGeometry.Coh
