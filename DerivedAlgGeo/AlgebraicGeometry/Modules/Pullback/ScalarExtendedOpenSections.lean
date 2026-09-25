/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.FixedBaseOpenSections
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Scalar extension of the pullback unit on open sections

For compatible maps `R ⟶ Γ(Y, ⊤)` and `A ⟶ Γ(Z, ⊤)`, the actual
pullback adjunction unit on an arbitrary open `U` transposes to an
`A`-linear map from extended sections of `M` on `U` to sections of
`f⁺ M` on `f ⁻¹ᵁ U`. This is an underived map; no localization or
isomorphism assertion is made.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped ChangeOfRings TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R A : CommRingCat.{u}} {Y Z : Scheme.{u}}
  (φ : R ⟶ Γ(Y, ⊤)) (f : Z ⟶ Y) (M : Y.Modules)
  (a : R ⟶ A) (ψ : A ⟶ Γ(Z, ⊤))

private noncomputable def fixedBaseOpenSections_restrictScalars
    (U : Y.Opens) (compat : φ ≫ f.appTop = a ≫ ψ) (N : Z.Modules) :
    (fixedBaseSectionsFunctor Z (φ ≫ f.appTop) (f ⁻¹ᵁ U)).obj N ⟶
      (ModuleCat.restrictScalars a.hom).obj
        ((fixedBaseSectionsFunctor Z ψ (f ⁻¹ᵁ U)).obj N) := by
  let K := (fixedBaseSectionsFunctor Z (φ ≫ f.appTop) (f ⁻¹ᵁ U)).obj N
  let T := (fixedBaseSectionsFunctor Z ψ (f ⁻¹ᵁ U)).obj N
  letI : Module R K := K.isModule
  letI : Module R ((ModuleCat.restrictScalars a.hom).obj T) :=
    ((ModuleCat.restrictScalars a.hom).obj T).isModule
  exact ModuleCat.ofHom (X := K) (Y := (ModuleCat.restrictScalars a.hom).obj T)
    { toFun := fun x => x
      map_add' := by intros; rfl
      map_smul' := by
        intro r x
        change (K.smul r).hom x = (T.smul (a.hom r)).hom x
        have hK := modulesToFixedBaseSheaf_smul Z (φ ≫ f.appTop) N
          (f ⁻¹ᵁ U) r x
        have hT := modulesToFixedBaseSheaf_smul Z ψ N (f ⁻¹ᵁ U) (a.hom r) x
        change (K.smul r).hom x = _ at hK
        change (T.smul (a.hom r)).hom x = _ at hT
        rw [hK, hT]
        change (N.smul (Z.presheaf.map (f ⁻¹ᵁ U).leTop.op
          ((φ ≫ f.appTop).hom r))).hom (show Γ(N, f ⁻¹ᵁ U) from x) =
          (N.smul (Z.presheaf.map (f ⁻¹ᵁ U).leTop.op
            ((a ≫ ψ).hom r))).hom (show Γ(N, f ⁻¹ᵁ U) from x)
        rw [compat] }

/-- The change-of-scalars comparison on the same section carrier commutes
with restriction; this is separate from the pullback unit. -/
private theorem fixedBaseOpenSections_restrictScalars_restrict
    {U V : Y.Opens} (h : U ≤ V)
    (compat : φ ≫ f.appTop = a ≫ ψ) (N : Z.Modules) :
    fixedBaseOpenSections_restrictScalars φ f a ψ V compat N ≫
      (ModuleCat.restrictScalars a.hom).map
        (((modulesToFixedBaseSheaf Z ψ).obj N).presheaf.map
          ((Opens.map f.base).map (homOfLE h)).op) =
      (((modulesToFixedBaseSheaf Z (φ ≫ f.appTop)).obj N).presheaf.map
          ((Opens.map f.base).map (homOfLE h)).op) ≫
        fixedBaseOpenSections_restrictScalars φ f a ψ U compat N := by
  ext x
  rfl

/-- The actual open-section pullback unit, transposed across extension of scalars. -/
noncomputable def fixedBasePullbackOpenAfterExtension (U : Y.Opens)
    (compat : φ ≫ f.appTop = a ≫ ψ) :
    (ModuleCat.extendScalars a.hom).obj
        ((fixedBaseSectionsFunctor Y φ U).obj M) ⟶
      (fixedBaseSectionsFunctor Z ψ (f ⁻¹ᵁ U)).obj ((pullback f).obj M) := by
  let N := (pullback f).obj M
  let k := fixedBaseOpenSections_restrictScalars φ f a ψ U compat N
  exact ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars a.hom
    (fixedBasePullbackOpen φ f M U ≫ k)

/-- On `1 ⊗ x`, the extended map is literally the ordinary pullback unit at `U`. -/
theorem fixedBasePullbackOpenAfterExtension_one_tmul (U : Y.Opens)
    (compat : φ ≫ f.appTop = a ≫ ψ) (x : Γ(M, U)) :
    (fixedBasePullbackOpenAfterExtension φ f M a ψ U compat).hom
        ((1 : A) ⊗ₜ[R,(a.hom)] x) =
      (((pullbackPushforwardAdjunction f).unit.app M).app U) x := by
  let T := (fixedBaseSectionsFunctor Z ψ (f ⁻¹ᵁ U)).obj ((pullback f).obj M)
  letI : Module R A := Module.compHom A a.hom
  letI : Module R T := Module.compHom T a.hom
  unfold fixedBasePullbackOpenAfterExtension
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
  erw [TensorProduct.lift.tmul]
  change (1 : A) • ((fixedBasePullbackOpen φ f M U ≫
    fixedBaseOpenSections_restrictScalars φ f a ψ U compat ((pullback f).obj M)).hom x) = _
  rw [one_smul]
  simp only [ModuleCat.comp_apply, fixedBasePullbackOpen_apply]
  rfl

/-- The scalar-extended actual pullback unit commutes with restriction of
opens. The proof transposes the already proved `R`-linear restriction square
through the extension/restriction-of-scalars adjunction. -/
theorem fixedBasePullbackOpenAfterExtension_restrict
    {U V : Y.Opens} (h : U ≤ V)
    (compat : φ ≫ f.appTop = a ≫ ψ) :
    fixedBasePullbackOpenAfterExtension φ f M a ψ V compat ≫
        (((modulesToFixedBaseSheaf Z ψ).obj ((pullback f).obj M)).presheaf.map
          ((Opens.map f.base).map (homOfLE h)).op) =
      (ModuleCat.extendScalars a.hom).map
          (((modulesToFixedBaseSheaf Y φ).obj M).presheaf.map (homOfLE h).op) ≫
        fixedBasePullbackOpenAfterExtension φ f M a ψ U compat := by
  let N := (pullback f).obj M
  let rY := (((modulesToFixedBaseSheaf Y φ).obj M).presheaf.map (homOfLE h).op)
  let rZ := (((modulesToFixedBaseSheaf Z ψ).obj N).presheaf.map
    ((Opens.map f.base).map (homOfLE h)).op)
  let rZR := (((modulesToFixedBaseSheaf Z (φ ≫ f.appTop)).obj N).presheaf.map
    ((Opens.map f.base).map (homOfLE h)).op)
  let kU := fixedBaseOpenSections_restrictScalars φ f a ψ U compat N
  let kV := fixedBaseOpenSections_restrictScalars φ f a ψ V compat N
  let pU := fixedBasePullbackOpen φ f M U
  let pV := fixedBasePullbackOpen φ f M V
  have hbase : pV ≫ rZR = rY ≫ pU :=
    fixedBasePullbackOpen_restrict φ f M h
  have hk : kV ≫ (ModuleCat.restrictScalars a.hom).map rZ =
      rZR ≫ kU :=
    fixedBaseOpenSections_restrictScalars_restrict φ f a ψ h compat N
  have hstep : pV ≫ (rZR ≫ kU) =
      pV ≫ (kV ≫ (ModuleCat.restrictScalars a.hom).map rZ) :=
    congrArg (fun q => pV ≫ q) hk.symm
  have hR : rY ≫ (pU ≫ kU) = (pV ≫ kV) ≫
      (ModuleCat.restrictScalars a.hom).map rZ := by
    have hleft : rY ≫ (pU ≫ kU) = pV ≫ (rZR ≫ kU) :=
      (Category.assoc rY pU kU).symm |>.trans
        ((congrArg (fun q => q ≫ kU) hbase.symm).trans
          (Category.assoc pV rZR kU))
    have hright : pV ≫ (kV ≫ (ModuleCat.restrictScalars a.hom).map rZ) =
        (pV ≫ kV) ≫ (ModuleCat.restrictScalars a.hom).map rZ :=
      (Category.assoc pV kV ((ModuleCat.restrictScalars a.hom).map rZ)).symm
    exact hleft.trans (hstep.trans hright)
  let adj := ModuleCat.extendRestrictScalarsAdj a.hom
  have hA := adj.homEquiv_naturality_right_square rY (pU ≫ kU)
    (pV ≫ kV) rZ hR
  simp only [adj, ModuleCat.extendRestrictScalarsAdj,
    Adjunction.mk'_homEquiv,
    ModuleCat.ExtendRestrictScalarsAdj.homEquiv_symm_apply] at hA
  convert hA.symm using 1 <;> rfl

/-- The commutative square underlying a Cartesian base-change square supplies
the scalar compatibility for the actual open-section pullback unit. -/
theorem fixedBasePullbackOpenAfterExtension_compat_of_isPullback
    {p : Y ⟶ Spec R} {q : Z ⟶ Spec A}
    (h : IsPullback f q p (Spec.map a)) :
    ((Scheme.ΓSpecIso R).inv ≫ p.appTop) ≫ f.appTop =
      a ≫ ((Scheme.ΓSpecIso A).inv ≫ q.appTop) := by
  calc
    ((Scheme.ΓSpecIso R).inv ≫ p.appTop) ≫ f.appTop =
        (Scheme.ΓSpecIso R).inv ≫ (f ≫ p).appTop := by
          rw [Scheme.Hom.comp_appTop, Category.assoc]
    _ = (Scheme.ΓSpecIso R).inv ≫ (q ≫ Spec.map a).appTop := by rw [h.w]
    _ = ((Scheme.ΓSpecIso R).inv ≫ (Spec.map a).appTop) ≫ q.appTop := by
          rw [Scheme.Hom.comp_appTop, Category.assoc]
    _ = a ≫ ((Scheme.ΓSpecIso A).inv ≫ q.appTop) := by
          rw [← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

/-- The actual scalar-extended pullback unit for a Cartesian square over
affine spectra, with its scalar action determined by the two structure maps. -/
noncomputable def fixedBasePullbackOpenOfIsPullback
    (p : Y ⟶ Spec R) (q : Z ⟶ Spec A)
    (h : IsPullback f q p (Spec.map a)) (U : Y.Opens) :
    (ModuleCat.extendScalars a.hom).obj
        ((fixedBaseSectionsFunctor Y ((Scheme.ΓSpecIso R).inv ≫ p.appTop) U).obj M) ⟶
      (fixedBaseSectionsFunctor Z ((Scheme.ΓSpecIso A).inv ≫ q.appTop)
        (f ⁻¹ᵁ U)).obj ((pullback f).obj M) :=
  fixedBasePullbackOpenAfterExtension
    ((Scheme.ΓSpecIso R).inv ≫ p.appTop) f M a
    ((Scheme.ΓSpecIso A).inv ≫ q.appTop) U
    (fixedBasePullbackOpenAfterExtension_compat_of_isPullback f a h)

/-- The square-specialized unit sends a tensor generator to the component of
the scheme-module pullback adjunction unit. -/
theorem fixedBasePullbackOpenOfIsPullback_one_tmul
    (p : Y ⟶ Spec R) (q : Z ⟶ Spec A)
    (h : IsPullback f q p (Spec.map a)) (U : Y.Opens) (x : Γ(M, U)) :
    (fixedBasePullbackOpenOfIsPullback f M a p q h U).hom
        ((1 : A) ⊗ₜ[R,(a.hom)] x) =
      (((pullbackPushforwardAdjunction f).unit.app M).app U) x :=
  fixedBasePullbackOpenAfterExtension_one_tmul
    ((Scheme.ΓSpecIso R).inv ≫ p.appTop) f M a
    ((Scheme.ΓSpecIso A).inv ≫ q.appTop) U
    (fixedBasePullbackOpenAfterExtension_compat_of_isPullback f a h) x

/-- The unit obtained from the Cartesian square commutes with restriction to
every open, including affine opens, without a chosen scalar compatibility. -/
theorem fixedBasePullbackOpenOfIsPullback_restrict
    (p : Y ⟶ Spec R) (q : Z ⟶ Spec A)
    (h : IsPullback f q p (Spec.map a))
    {U V : Y.Opens} (hUV : U ≤ V) :
    fixedBasePullbackOpenOfIsPullback f M a p q h V ≫
        (((modulesToFixedBaseSheaf Z ((Scheme.ΓSpecIso A).inv ≫ q.appTop)).obj
          ((pullback f).obj M)).presheaf.map
            ((Opens.map f.base).map (homOfLE hUV)).op) =
      (ModuleCat.extendScalars a.hom).map
          (((modulesToFixedBaseSheaf Y ((Scheme.ΓSpecIso R).inv ≫ p.appTop)).obj
            M).presheaf.map (homOfLE hUV).op) ≫
        fixedBasePullbackOpenOfIsPullback f M a p q h U :=
  fixedBasePullbackOpenAfterExtension_restrict
    ((Scheme.ΓSpecIso R).inv ≫ p.appTop) f M a
    ((Scheme.ΓSpecIso A).inv ≫ q.appTop) hUV
    (fixedBasePullbackOpenAfterExtension_compat_of_isPullback f a h)

end AlgebraicGeometry.Scheme.Modules
