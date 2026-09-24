/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.Localization.FixedTargetArrow
import DerivedAlgGeo.Algebra.Module.Localization.FixedTerminalThreeTerm
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.AffineSpec
import DerivedAlgGeo.CategoryTheory.SubobjectEquivalence
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.CategoryTheory.Whiskering

/-!
# Fixed-target arrows and three-term diagrams for affine coherent localization

This file transfers the fixed-target module arrow and zero-composite three-term theorems
to coherent sheaves on affine noetherian schemes. It concerns ordinary coherent pullback,
not derived pullback, a bounded component, or an arbitrary t-heart.
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

private theorem finiteExtendScalars_fixedTerminalThreeTerm [IsNoetherianRing R]
    (S : Submonoid R) [IsLocalization S A]
    (M : FGModuleCat.{u} R) (N₀ N₁ : FGModuleCat.{u} A)
    (d : N₀ ⟶ N₁) (β : N₁ ⟶ (finiteExtendScalars (R := R) (A := A)).obj M)
    (hz : d ≫ β = 0) :
    ∃ (Y₀ Y₁ : FGModuleCat.{u} R) (g : Y₀ ⟶ Y₁) (f : Y₁ ⟶ M)
      (e₀ : N₀ ≅ (finiteExtendScalars (R := R) (A := A)).obj Y₀)
      (e₁ : N₁ ≅ (finiteExtendScalars (R := R) (A := A)).obj Y₁),
      g ≫ f = 0 ∧
      d ≫ e₁.hom = e₀.hom ≫ (finiteExtendScalars (R := R) (A := A)).map g ∧
      β = e₁.hom ≫ (finiteExtendScalars (R := R) (A := A)).map f := by
  letI : Module R N₀ := Module.compHom N₀ (algebraMap R A)
  letI : Module R N₁ := Module.compHom N₁ (algebraMap R A)
  letI : Module.Finite A N₀ := N₀.property
  letI : Module.Finite A N₁ := N₁.property
  let alg : Algebra R A := inferInstance
  let hLoc : @IsLocalization R _ S A _ alg := inferInstance
  have hAlgEq : (algebraMap R A).toAlgebra = alg := toAlgebra_algebraMap
  letI : Algebra R A := (algebraMap R A).toAlgebra
  haveI : IsLocalization S A := by
    exact (congrArg (fun a : Algebra R A => @IsLocalization R _ S A _ a)
      hAlgEq).mpr hLoc
  letI : IsScalarTower R A N₀ := IsScalarTower.of_compHom R A N₀
  letI : IsScalarTower R A N₁ := IsScalarTower.of_compHom R A N₁
  have hzLinear : β.hom.hom.comp d.hom.hom = 0 := by
    have h := congrArg (fun t : N₀ ⟶ (finiteExtendScalars (R := R) (A := A)).obj M =>
      t.hom.hom) hz
    exact h
  obtain ⟨L₀, L₁, hfp₀, hfp₁, d₀, f, e₀, e₁, hz₀, hd, hβ⟩ :=
    Module.exists_finitely_presented_fixedTerminalThreeTerm_of_isLocalization
      (R := R) (A := A) (M₀ := N₀) (M₁ := N₁) (T := M) S
      d.hom.hom β.hom.hom hzLinear
  letI : Module.FinitePresentation R L₀ := hfp₀
  letI : Module.FinitePresentation R L₁ := hfp₁
  let Y₀ : FGModuleCat.{u} R := FGModuleCat.of R L₀
  let Y₁ : FGModuleCat.{u} R := FGModuleCat.of R L₁
  let g : Y₀ ⟶ Y₁ := ConcreteCategory.ofHom d₀
  let k : Y₁ ⟶ M := ConcreteCategory.ofHom f
  let eCat₀ : N₀ ≅ (finiteExtendScalars (R := R) (A := A)).obj Y₀ :=
    { hom := ConcreteCategory.ofHom e₀.toLinearMap
      inv := ConcreteCategory.ofHom e₀.symm.toLinearMap
      hom_inv_id := by ext x; exact e₀.left_inv x
      inv_hom_id := by ext x; exact e₀.right_inv x }
  let eCat₁ : N₁ ≅ (finiteExtendScalars (R := R) (A := A)).obj Y₁ :=
    { hom := ConcreteCategory.ofHom e₁.toLinearMap
      inv := ConcreteCategory.ofHom e₁.symm.toLinearMap
      hom_inv_id := by ext x; exact e₁.left_inv x
      inv_hom_id := by ext x; exact e₁.right_inv x }
  have hmap : ∀ {L T : Type u} [AddCommGroup L] [Module R L]
      [AddCommGroup T] [Module R T] (q : L →ₗ[R] T),
      (IsLocalizedModule.mapExtendScalars S
        (TensorProduct.mk R A L 1) (TensorProduct.mk R A T 1) A) q =
        ((ModuleCat.extendScalars (algebraMap R A)).map
          (ModuleCat.ofHom q)).hom := by
    intro L T _ _ _ _ q
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
          (TensorProduct.mk R A L 1) (TensorProduct.mk R A T 1) A) q)
          ((TensorProduct.mk R A L 1) l) =
        ((ModuleCat.extendScalars (algebraMap R A)).map
          (ModuleCat.ofHom q)).hom ((TensorProduct.mk R A L 1) l)
      rw [IsLocalizedModule.mapExtendScalars_apply_apply,
        IsLocalizedModule.map_apply]
      rfl
    | add x y hx hy =>
      simpa only [IsLocalizedModule.mapExtendScalars_apply_apply, _root_.map_add]
        using congrArg₂ HAdd.hAdd hx hy
  have hzCat : g ≫ k = 0 := by
    apply FGModuleCat.hom_ext
    exact hz₀
  have hdCat : d ≫ eCat₁.hom = eCat₀.hom ≫
      (finiteExtendScalars (R := R) (A := A)).map g := by
    apply FGModuleCat.hom_ext
    change e₁.toLinearMap.comp d.hom.hom =
      (((ModuleCat.extendScalars (algebraMap R A)).map (ModuleCat.ofHom d₀)).hom).comp
        e₀.toLinearMap
    rw [← hmap d₀]
    exact hd
  have hβCat : β = eCat₁.hom ≫
      (finiteExtendScalars (R := R) (A := A)).map k := by
    apply FGModuleCat.hom_ext
    change β.hom.hom =
      (((ModuleCat.extendScalars (algebraMap R A)).map (ModuleCat.ofHom f)).hom).comp
        e₁.toLinearMap
    rw [← hmap f]
    exact hβ
  exact ⟨Y₀, Y₁, g, k, eCat₀, eCat₁, hzCat, hdCat, hβCat⟩

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

/-- A zero-composite three-term diagram of coherent sheaves over an affine noetherian
localization descends with its terminal coherent sheaf `E` fixed. Both arrows agree with
ordinary coherent pullback through the displayed isomorphisms. This is underived. -/
theorem exists_fixedTerminalThreeTerm_pullbackSpecMap_of_isLocalization
    [IsNoetherianRing R] (S : Submonoid R) [IsLocalization S A]
    (E : Coh (Spec (CommRingCat.of R)))
    (N₀ N₁ : Coh (Spec (CommRingCat.of A)))
    (d : N₀ ⟶ N₁)
    (β : N₁ ⟶ (Coh.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj E)
    (hz : d ≫ β = 0) :
    ∃ (L₀ L₁ : Coh (Spec (CommRingCat.of R)))
      (d₀ : L₀ ⟶ L₁) (f : L₁ ⟶ E)
      (e₀ : N₀ ≅ (Coh.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj L₀)
      (e₁ : N₁ ≅ (Coh.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj L₁),
      d₀ ≫ f = 0 ∧
      d ≫ e₁.hom = e₀.hom ≫ (Coh.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map d₀ ∧
      β = e₁.hom ≫ (Coh.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map f := by
  letI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
  let ER := Coh.affineEquivalence (R := CommRingCat.of R)
  let EA := Coh.affineEquivalence (R := CommRingCat.of A)
  let FR := FGModuleCat.affineTilde (R := CommRingCat.of R)
  let FA := FGModuleCat.affineTilde (R := CommRingCat.of A)
  let F := Coh.pullback (Spec.map (ringMap (R := R) (A := A)))
  let G := finiteExtendScalars (R := R) (A := A)
  let α := affineTildePullbackIso (R := R) (A := A)
  let M : FGModuleCat.{u} R := ER.functor.obj E
  let M₀ : FGModuleCat.{u} A := EA.functor.obj N₀
  let M₁ : FGModuleCat.{u} A := EA.functor.obj N₁
  let cR : E ≅ FR.obj M := ER.unitIso.app E
  let c₀ : N₀ ≅ FA.obj M₀ := EA.unitIso.app N₀
  let c₁ : N₁ ≅ FA.obj M₁ := EA.unitIso.app N₁
  letI : FA.Full := EA.fullyFaithfulInverse.full
  letI : FA.Faithful := EA.fullyFaithfulInverse.faithful
  let dG : M₀ ⟶ M₁ := FA.preimage (c₀.inv ≫ d ≫ c₁.hom)
  let βG : M₁ ⟶ G.obj M :=
    FA.preimage (c₁.inv ≫ β ≫ F.map cR.hom ≫ (α.app M).hom)
  have hdFA : FA.map dG = c₀.inv ≫ d ≫ c₁.hom := FA.map_preimage _
  have hβFA : FA.map βG =
      c₁.inv ≫ β ≫ F.map cR.hom ≫ (α.app M).hom := FA.map_preimage _
  have hzG : dG ≫ βG = 0 := by
    apply FA.map_injective
    rw [Functor.map_comp, hdFA, hβFA, Functor.map_zero]
    calc
      (c₀.inv ≫ d ≫ c₁.hom) ≫
          (c₁.inv ≫ β ≫ F.map cR.hom ≫ (α.app M).hom) =
          c₀.inv ≫ (d ≫ β) ≫ F.map cR.hom ≫ (α.app M).hom := by
        calc
          _ = c₀.inv ≫ d ≫ (c₁.hom ≫ c₁.inv) ≫ β ≫
              F.map cR.hom ≫ (α.app M).hom := by simp only [Category.assoc]
          _ = c₀.inv ≫ d ≫ β ≫ F.map cR.hom ≫ (α.app M).hom := by
            rw [c₁.hom_inv_id]
            simp
          _ = _ := by simp only [Category.assoc]
      _ = 0 := by rw [hz]; simp
  obtain ⟨Y₀, Y₁, g, k, e₀, e₁, hzY, hdG, hβG⟩ :=
    finiteExtendScalars_fixedTerminalThreeTerm (R := R) (A := A)
      S M M₀ M₁ dG βG hzG
  let L₀ : Coh (Spec (CommRingCat.of R)) := FR.obj Y₀
  let L₁ : Coh (Spec (CommRingCat.of R)) := FR.obj Y₁
  let dCoh : L₀ ⟶ L₁ := FR.map g
  let fCoh : L₁ ⟶ E := FR.map k ≫ cR.inv
  let eCoh₀ : N₀ ≅ F.obj L₀ :=
    c₀ ≪≫ FA.mapIso e₀ ≪≫ (α.app Y₀).symm
  let eCoh₁ : N₁ ≅ F.obj L₁ :=
    c₁ ≪≫ FA.mapIso e₁ ≪≫ (α.app Y₁).symm
  refine ⟨L₀, L₁, dCoh, fCoh, eCoh₀, eCoh₁, ?_, ?_, ?_⟩
  · change FR.map g ≫ FR.map k ≫ cR.inv = 0
    have hmapzero : FR.map g ≫ FR.map k = 0 := by
      calc
        FR.map g ≫ FR.map k = FR.map (g ≫ k) := (FR.map_comp g k).symm
        _ = FR.map 0 := by rw [hzY]
        _ = 0 := by
          apply (Coh.ι (Spec (CommRingCat.of R))).map_injective
          change (AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
            ((ModuleCat.isFG R).ι.map (0 : Y₀ ⟶ M)) = 0
          have hιzero : (ModuleCat.isFG R).ι.map (0 : Y₀ ⟶ M) = 0 := rfl
          rw [hιzero]
          exact AlgebraicGeometry.tilde.map_zero
    rw [← Category.assoc, hmapzero]
    exact Limits.zero_comp
  · change d ≫ eCoh₁.hom = eCoh₀.hom ≫ F.map dCoh
    have hαg : FA.map (G.map g) ≫ (α.app Y₁).inv =
        (α.app Y₀).inv ≫ F.map (FR.map g) := by
      convert α.inv.naturality g using 1; rfl
    have hdGFA : FA.map dG ≫ FA.map e₁.hom =
        FA.map e₀.hom ≫ FA.map (G.map g) := by
      simpa only [← Functor.map_comp] using congrArg FA.map hdG
    have hdC : d = c₀.hom ≫ FA.map dG ≫ c₁.inv := by
      rw [hdFA]
      calc
        d = (c₀.hom ≫ c₀.inv) ≫ d ≫ (c₁.hom ≫ c₁.inv) := by simp
        _ = c₀.hom ≫ (c₀.inv ≫ d ≫ c₁.hom) ≫ c₁.inv := by
          simp only [Category.assoc]
    change d ≫ (c₁.hom ≫ FA.map e₁.hom ≫ (α.app Y₁).inv) =
      (c₀.hom ≫ FA.map e₀.hom ≫ (α.app Y₀).inv) ≫ F.map (FR.map g)
    calc
      d ≫ (c₁.hom ≫ FA.map e₁.hom ≫ (α.app Y₁).inv) =
          c₀.hom ≫ FA.map dG ≫ FA.map e₁.hom ≫ (α.app Y₁).inv := by
        rw [hdC]
        calc
          _ = c₀.hom ≫ FA.map dG ≫ (c₁.inv ≫ c₁.hom) ≫
              FA.map e₁.hom ≫ (α.app Y₁).inv := by simp only [Category.assoc]
          _ = _ := by rw [c₁.inv_hom_id]; simp only [Category.id_comp]
      _ = c₀.hom ≫ FA.map e₀.hom ≫ FA.map (G.map g) ≫ (α.app Y₁).inv := by
        exact congrArg (fun t => c₀.hom ≫ t ≫ (α.app Y₁).inv) hdGFA
      _ = (c₀.hom ≫ FA.map e₀.hom ≫ (α.app Y₀).inv) ≫
          F.map (FR.map g) := by
        calc
          _ = c₀.hom ≫ FA.map e₀.hom ≫
              (FA.map (G.map g) ≫ (α.app Y₁).inv) := by rfl
          _ = c₀.hom ≫ FA.map e₀.hom ≫
              ((α.app Y₀).inv ≫ F.map (FR.map g)) := by
            exact congrArg (fun t => c₀.hom ≫ FA.map e₀.hom ≫ t) hαg
          _ = _ := by rfl
  · change β = eCoh₁.hom ≫ F.map fCoh
    have hαk : FA.map (G.map k) ≫ (α.app M).inv =
        (α.app Y₁).inv ≫ F.map (FR.map k) := by
      convert α.inv.naturality k using 1; rfl
    have hβGFA : FA.map βG = FA.map e₁.hom ≫ FA.map (G.map k) := by
      rw [hβG, Functor.map_comp]
    symm
    calc
      eCoh₁.hom ≫ F.map fCoh =
          c₁.hom ≫ FA.map e₁.hom ≫ (α.app Y₁).inv ≫
            F.map (FR.map k) ≫ F.map cR.inv := by
        simp only [eCoh₁, fCoh, Iso.trans_hom, Functor.map_comp,
          Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
        rfl
      _ = c₁.hom ≫ FA.map e₁.hom ≫
            ((α.app Y₁).inv ≫ F.map (FR.map k)) ≫ F.map cR.inv := by
        simp only [Category.assoc]
      _ = c₁.hom ≫ FA.map e₁.hom ≫
            (FA.map (G.map k) ≫ (α.app M).inv) ≫ F.map cR.inv := by
        exact congrArg
          (fun t => c₁.hom ≫ FA.map e₁.hom ≫ t ≫ F.map cR.inv) hαk.symm
      _ = c₁.hom ≫ (FA.map e₁.hom ≫ FA.map (G.map k)) ≫
            (α.app M).inv ≫ F.map cR.inv := by
        simp only [Category.assoc]
      _ = c₁.hom ≫ FA.map βG ≫ (α.app M).inv ≫ F.map cR.inv := by
        exact congrArg
          (fun t => c₁.hom ≫ t ≫ (α.app M).inv ≫ F.map cR.inv) hβGFA.symm
      _ = c₁.hom ≫ c₁.inv ≫ β ≫ F.map cR.hom ≫
            (α.app M).hom ≫ (α.app M).inv ≫ F.map cR.inv := by
        rw [hβFA]
        cat_disch
      _ = c₁.hom ≫ c₁.inv ≫ β ≫ F.map cR.hom ≫
            ((α.app M).hom ≫ (α.app M).inv) ≫ F.map cR.inv := by
        simp only [Category.assoc]
      _ = c₁.hom ≫ c₁.inv ≫ β ≫ F.map cR.hom ≫
            (𝟙 (F.obj (FR.obj M))) ≫ F.map cR.inv := by
        exact congrArg
          (fun t => c₁.hom ≫ c₁.inv ≫ β ≫ F.map cR.hom ≫ t ≫ F.map cR.inv)
          (α.app M).hom_inv_id
      _ = c₁.hom ≫ c₁.inv ≫ β ≫ F.map cR.hom ≫ F.map cR.inv := by
        cat_disch
      _ = c₁.hom ≫ c₁.inv ≫ β := by
        simp only [← F.map_comp, cR.hom_inv_id, F.map_id]
        cat_disch
      _ = β := by
        simp only [Iso.hom_inv_id_assoc]

end AlgebraicGeometry.Coh
