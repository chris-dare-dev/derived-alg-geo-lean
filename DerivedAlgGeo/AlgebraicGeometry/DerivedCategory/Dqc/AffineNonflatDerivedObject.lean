/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineNonflatExample
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectivePullback
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.Bounded
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The derived effect of the non-flat affine witness

This file computes one concrete effect of extension of scalars along the
non-flat map `ℤ → ZMod 2`. It gives an explicit two-term free resolution of
`ZMod 2`, proves that its degreewise scalar extension has nonzero homology in
degree `-1`, and identifies that calculation with the existing supported
affine K-projective pullback on this representative.

## Main definitions

- `ZModTwoNonflatDerived.twoTermResolution` is the explicit two-term free
  cochain resolution of `ZMod 2` over `ℤ`.
- `ZModTwoNonflatDerived.baseChangedResolution` is its degreewise scalar
  extension along `ℤ → ZMod 2`.
- `ZModTwoNonflatDerived.affineKProjectivePullbackObject` is the existing
  supported affine K-projective pullback applied to this representative.

## Main results

- `twoTermAugmentation_quasiIso` certifies the displayed resolution.
- `baseChangedResolution_homology_negOne_not_isZero` proves the explicit
  degree-minus-one effect after scalar extension.
- `torOneIsoRestrictScalarsBaseChangedResolutionHomologyNegOne` identifies
  the restricted degree-minus-one homology with Mathlib's fixed-left,
  derived-second-argument `Tor` for the displayed modules.
- `affineKProjectivePullbackObject_homology_negOne_not_isZero` transports the
  effect to the supported pullback object.

## Implementation notes

The calculation is deliberately affine and representative-level. It does
not assert a general scheme-level left-derived pullback, preservation of a
full `Dqc` locus, a relative-perfect preservation theorem, or a comparison
with an unformalized classical invariant.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace ZModTwoNonflatDerived

private abbrev zModule : ModuleCat ℤ := ModuleCat.of ℤ ℤ
private abbrev zmodTwoModule : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 2)
private abbrev zmodTwoTargetModule : ModuleCat (ZMod 2) := ModuleCat.of (ZMod 2) (ZMod 2)

private abbrev zmodTwoExtend : ModuleCat ℤ ⥤ ModuleCat (ZMod 2) :=
  ModuleCat.extendScalars zmodTwoRingMap.hom

private instance zmodTwoExtend_additive : zmodTwoExtend.Additive :=
  affineExtendScalars_additive zmodTwoRingMap

private def timesTwo : zModule ⟶ zModule :=
  ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ 2)

private def reductionModTwo : zModule ⟶ zmodTwoModule :=
  ModuleCat.ofHom (Int.castAddHom (ZMod 2)).toIntLinearMap

private def shortComplex : ShortComplex (ModuleCat ℤ) :=
  ModuleCat.shortComplexOfCompEqZero timesTwo.hom reductionModTwo.hom (by
    apply LinearMap.ext
    intro x
    change ((2 * x : ℤ) : ZMod 2) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨x, by ring⟩)

private theorem shortComplex_shortExact : shortComplex.ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (LinearMap.lsmul ℤ ℤ 2)
      (Int.castAddHom (ZMod 2)).toIntLinearMap
    intro x
    constructor
    · intro hx
      change (x : ZMod 2) = 0 at hx
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
      obtain ⟨y, hy⟩ := hx
      refine ⟨y, ?_⟩
      change 2 * y = x
      omega
    · rintro ⟨y, hy⟩
      change (x : ZMod 2) = 0
      change 2 * y = x at hy
      rw [← hy]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * y) 2).mpr ⟨y, by ring⟩
  · change Function.Injective (LinearMap.lsmul ℤ ℤ 2)
    exact LinearMap.lsmul_injective (by norm_num : (2 : ℤ) ≠ 0)
  · change Function.Surjective (Int.castAddHom (ZMod 2)).toIntLinearMap
    exact ZMod.intCast_surjective

private abbrev singleAtZero : ModuleCat ℤ ⥤ CochainComplex (ModuleCat ℤ) ℤ :=
  HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.up ℤ) 0

private def shortExactAtZero : ShortComplex (CochainComplex (ModuleCat ℤ) ℤ) :=
  shortComplex.map singleAtZero

private theorem shortExactAtZero_shortExact : shortExactAtZero.ShortExact :=
  shortComplex_shortExact.map_of_exact singleAtZero

private theorem shortExactAtZero_f : shortExactAtZero.f = singleAtZero.map timesTwo := rfl

/-- The explicit two-term free cochain resolution of `ZMod 2` over `ℤ`. -/
def twoTermResolution : CochainComplex (ModuleCat ℤ) ℤ :=
  CochainComplex.mappingCone shortExactAtZero.f

/-- The augmentation from the two-term free resolution to `ZMod 2[0]`. -/
def twoTermAugmentation : twoTermResolution ⟶ (singleAtZero.obj zmodTwoModule) :=
  CochainComplex.mappingCone.descShortComplex shortExactAtZero

/-- The explicit two-term augmentation is a quasi-isomorphism. -/
theorem twoTermAugmentation_quasiIso :
    QuasiIso twoTermAugmentation :=
  CochainComplex.mappingCone.quasiIso_descShortComplex shortExactAtZero_shortExact

/-- The resolution is strictly supported in degrees at most zero. -/
instance twoTermResolution_isStrictlyLE_zero : twoTermResolution.IsStrictlyLE 0 := by
  change (CochainComplex.mappingCone (singleAtZero.map timesTwo)).IsStrictlyLE 0
  letI : (singleAtZero.obj zModule).IsStrictlyLE 0 := inferInstance
  exact CochainComplex.isStrictlyLE_mappingCone (singleAtZero.map timesTwo) 0 0 0

/-- Every term of the explicit resolution is projective. -/
instance twoTermResolution_projective_X (n : ℤ) :
    Projective (twoTermResolution.X n) := by
  change Projective ((CochainComplex.mappingCone (singleAtZero.map timesTwo)).X n)
  exact Projective.of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (singleAtZero.map timesTwo) n (n + 1) rfl).symm inferInstance

/-- The resolution as a K-projective representative. -/
def kProjectiveRepresentative : KProjectiveHomotopyCategory (ModuleCat ℤ) :=
  KProjectiveHomotopyCategory.ofBoundedAboveProjectives twoTermResolution 0

/-- The same concrete complex in the supported bounded-above-projective lane. -/
def boundedAboveProjectiveRepresentative :
    BoundedAboveProjectiveHomotopyCategory (ModuleCat ℤ) :=
  ⟨(HomotopyCategory.quotient (ModuleCat ℤ) (ComplexShape.up ℤ)).obj twoTermResolution,
    by
      change ∃ d : ℤ, twoTermResolution.IsStrictlyLE d ∧
        ∀ n : ℤ, Projective (twoTermResolution.X n)
      exact ⟨0, inferInstance, fun n => inferInstance⟩⟩

/-- The supported affine bounded-above-projective representative after base change. -/
def supportedAffineBoundedAboveProjectiveRepresentative :
    BoundedAboveProjectiveHomotopyCategory (ModuleCat (ZMod 2)) :=
  (affineBoundedAboveProjectiveHomotopyPullback zmodTwoRingMap).obj
    boundedAboveProjectiveRepresentative

private abbrev baseChangedSingle : CochainComplex (ModuleCat (ZMod 2)) ℤ :=
  (zmodTwoExtend.mapHomologicalComplex (ComplexShape.up ℤ)).obj (singleAtZero.obj zModule)

/-- The degreewise scalar extension of the explicit two-term resolution. -/
abbrev baseChangedResolution : CochainComplex (ModuleCat (ZMod 2)) ℤ :=
  (zmodTwoExtend.mapHomologicalComplex (ComplexShape.up ℤ)).obj twoTermResolution

private abbrev baseChangedMap : baseChangedSingle ⟶ baseChangedSingle :=
  (zmodTwoExtend.mapHomologicalComplex (ComplexShape.up ℤ)).map shortExactAtZero.f

private def baseChangedConeIso :
    baseChangedResolution ≅ CochainComplex.mappingCone baseChangedMap :=
  CochainComplex.mappingCone.mapHomologicalComplexIso shortExactAtZero.f zmodTwoExtend

/-- The supported affine K-projective pullback of the explicit representative. -/
def affineKProjectivePullbackObject : DerivedCategory (ModuleCat (ZMod 2)) :=
  (affineKProjectivePullback zmodTwoRingMap).obj kProjectiveRepresentative

/-- The supported K-projective pullback is computed by degreewise scalar extension here. -/
def affineKProjectivePullbackObjectIso :
    affineKProjectivePullbackObject ≅ DerivedCategory.Q.obj baseChangedResolution := by
  simpa only [affineKProjectivePullbackObject,
    kProjectiveRepresentative, baseChangedResolution, zmodTwoExtend] using
    affineKProjectivePullbackObjIso zmodTwoRingMap twoTermResolution 0

private abbrev zmodTwoAsZModule : ModuleCat ℤ :=
  (ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).obj zmodTwoTargetModule

private def zmodTwoOneAsZModule : zmodTwoAsZModule :=
  show ZMod 2 from 1

private theorem extend_timesTwo_eq_zero : zmodTwoExtend.map timesTwo = 0 := by
  change zmodTwoExtend.map ((2 : ℤ) • 𝟙 zModule) = 0
  rw [Functor.map_zsmul, zmodTwoExtend.map_id]
  change (2 : ℤ) • 𝟙 (zmodTwoExtend.obj zModule) = 0
  ext x
  change ((2 • 𝟙 (zmodTwoExtend.obj zModule)).hom)
      (zmodTwoOneAsZModule ⊗ₜ[ℤ] x) = 0
  simp only [ModuleCat.hom_zsmul, ModuleCat.hom_id,
    LinearMap.smul_apply, LinearMap.id_apply]
  rw [two_zsmul]
  change zmodTwoOneAsZModule ⊗ₜ[ℤ] x + zmodTwoOneAsZModule ⊗ₜ[ℤ] x = 0
  rw [← TensorProduct.add_tmul]
  rw [show zmodTwoOneAsZModule + zmodTwoOneAsZModule = 0 by
    change (2 : ZMod 2) = 0
    exact ZMod.natCast_self 2, TensorProduct.zero_tmul]

private def extendZIso : zmodTwoExtend.obj zModule ≅ zmodTwoTargetModule := by
  let algebra : Algebra ℤ (ZMod 2) := zmodTwoRingMap.hom.toAlgebra
  let sourceModule : Module ℤ zmodTwoAsZModule := ModuleCat.isModule zmodTwoAsZModule
  let targetModule : Module (ZMod 2) zmodTwoAsZModule := inferInstance
  let tower : @IsScalarTower ℤ (ZMod 2) zmodTwoAsZModule
      algebra.toSMul targetModule.toSMul sourceModule.toSMul := by
    exact @IsScalarTower.mk ℤ (ZMod 2) zmodTwoAsZModule
      algebra.toSMul targetModule.toSMul sourceModule.toSMul (by
        intro r s m
        change (zmodTwoRingMap.hom r * s) • m = zmodTwoRingMap.hom r • (s • m)
        exact mul_smul _ _ _)
  exact (@TensorProduct.AlgebraTensorModule.rid ℤ (ZMod 2) zmodTwoAsZModule
    _ _ algebra _ sourceModule targetModule tower).toModuleIso

private def baseChangedSingleIso :
    baseChangedSingle ≅
      (HomologicalComplex.single (ModuleCat (ZMod 2)) (ComplexShape.up ℤ) 0).obj
        (zmodTwoExtend.obj zModule) :=
  (HomologicalComplex.singleMapHomologicalComplex zmodTwoExtend (ComplexShape.up ℤ) 0).app zModule

private theorem baseChangedSingle_isZero_X (i : ℤ) (hi : i ≠ 0) :
    IsZero (baseChangedSingle.X i) := by
  apply IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (zmodTwoExtend.obj zModule) i hi)
  exact (HomologicalComplex.eval (ModuleCat (ZMod 2)) (ComplexShape.up ℤ) i).mapIso
    baseChangedSingleIso

private theorem extendZ_not_isZero : ¬ IsZero (zmodTwoExtend.obj zModule) := by
  intro h
  have h' : IsZero zmodTwoTargetModule := h.of_iso extendZIso.symm
  rw [IsZero.iff_id_eq_zero] at h'
  have := congrArg (fun f => f (1 : ZMod 2)) h'
  norm_num at this

private theorem baseChangedMap_eq_zero : baseChangedMap = 0 := by
  let e := HomologicalComplex.singleMapHomologicalComplex zmodTwoExtend
    (ComplexShape.up ℤ) 0
  have h_naturality :
      (zmodTwoExtend.mapHomologicalComplex (ComplexShape.up ℤ)).map shortExactAtZero.f ≫
          e.hom.app zModule =
        e.hom.app zModule ≫
          (HomologicalComplex.single (ModuleCat (ZMod 2)) (ComplexShape.up ℤ) 0).map
            (zmodTwoExtend.map timesTwo) := by
    rw [shortExactAtZero_f]
    exact e.hom.naturality timesTwo
  apply (cancel_mono (e.hom.app zModule)).mp
  change (zmodTwoExtend.mapHomologicalComplex (ComplexShape.up ℤ)).map shortExactAtZero.f ≫
    e.hom.app zModule = 0 ≫ e.hom.app zModule
  rw [h_naturality, zero_comp]
  rw [extend_timesTwo_eq_zero, Functor.map_zero]
  exact comp_zero

private abbrev baseChangedCone : CochainComplex (ModuleCat (ZMod 2)) ℤ :=
  CochainComplex.mappingCone baseChangedMap

private theorem baseChangedCone_isZero_X_negTwo : IsZero (baseChangedCone.X (-2)) :=
  (CochainComplex.mappingCone.isZero_X_iff baseChangedMap (-2)).mpr
    ⟨by simpa using baseChangedSingle_isZero_X (-1) (by omega),
      baseChangedSingle_isZero_X (-2) (by omega)⟩

private theorem baseChangedSingle_d_negOne_zero : baseChangedSingle.d (-1) 0 = 0 :=
  (baseChangedSingle_isZero_X (-1) (by omega)).eq_zero_of_src _

private theorem baseChangedSingle_d_zero_one_zero : baseChangedSingle.d 0 1 = 0 :=
  (baseChangedSingle_isZero_X 1 (by omega)).eq_zero_of_tgt _

private theorem baseChangedMap_f_zero (i : ℤ) : baseChangedMap.f i = 0 := by
  simpa using congrArg (fun f => f.f i) baseChangedMap_eq_zero

private theorem baseChangedCone_d_negOne_zero : baseChangedCone.d (-1) 0 = 0 := by
  apply CochainComplex.mappingCone.ext_from baseChangedMap 0 (-1) (by omega)
  · rw [CochainComplex.mappingCone.inl_v_d baseChangedMap 0 (-1) 1 (by omega) (by omega),
      baseChangedMap_f_zero,
      zero_comp, baseChangedSingle_d_zero_one_zero, zero_comp, sub_zero, comp_zero]
  · rw [CochainComplex.mappingCone.inr_f_d, baseChangedSingle_d_negOne_zero,
      zero_comp, comp_zero]

private theorem baseChangedCone_X_negOne_not_isZero : ¬ IsZero (baseChangedCone.X (-1)) := by
  intro h
  have hbase : IsZero (baseChangedSingle.X 0) := by
    rw [IsZero.iff_id_eq_zero]
    rw [← CochainComplex.mappingCone.inl_v_fst_v baseChangedMap 0 (-1) (by omega)]
    have hinl : (CochainComplex.mappingCone.inl baseChangedMap).v 0 (-1) (by omega) = 0 :=
      h.eq_zero_of_tgt _
    rw [hinl]
    simp
  have hsingle : IsZero
      (((HomologicalComplex.single (ModuleCat (ZMod 2)) (ComplexShape.up ℤ) 0).obj
        (zmodTwoExtend.obj zModule)).X 0) :=
    hbase.of_iso
      ((HomologicalComplex.eval (ModuleCat (ZMod 2)) (ComplexShape.up ℤ) 0).mapIso
        baseChangedSingleIso).symm
  apply extendZ_not_isZero
  exact hsingle.of_iso
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (zmodTwoExtend.obj zModule)).symm

private theorem baseChangedCone_not_exactAt_negOne : ¬ baseChangedCone.ExactAt (-1) := by
  intro h
  apply baseChangedCone_X_negOne_not_isZero
  have h' : (baseChangedCone.sc' (-2) (-1) 0).Exact :=
    ShortComplex.exact_of_iso
      (baseChangedCone.isoSc' (-2) (-1) 0 (by norm_num) (by norm_num)) h
  apply h'.isZero_of_both_zeros
  · exact baseChangedCone_isZero_X_negTwo.eq_zero_of_src _
  · change baseChangedCone.d (-1) 0 = 0
    exact baseChangedCone_d_negOne_zero

private theorem baseChangedCone_homology_negOne_not_isZero :
    ¬ IsZero (baseChangedCone.homology (-1)) := by
  intro h
  apply baseChangedCone_not_exactAt_negOne
  exact (HomologicalComplex.exactAt_iff_isZero_homology (K := baseChangedCone) (-1)).mpr h

/-- Degreewise scalar extension of the explicit resolution has nonzero `H^{-1}`. -/
theorem baseChangedResolution_homology_negOne_not_isZero :
    ¬ IsZero (baseChangedResolution.homology (-1)) := by
  intro h
  apply baseChangedCone_homology_negOne_not_isZero
  exact h.of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat (ZMod 2)) (ComplexShape.up ℤ) (-1)).mapIso
      baseChangedConeIso).symm

/-- The supported affine K-projective pullback object of this resolution has nonzero `H^{-1}`. -/
theorem affineKProjectivePullbackObject_homology_negOne_not_isZero :
    ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat (ZMod 2)) (-1)).obj
      affineKProjectivePullbackObject) := by
  intro h
  apply baseChangedResolution_homology_negOne_not_isZero
  have hQ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat (ZMod 2)) (-1)).obj
      (DerivedCategory.Q.obj baseChangedResolution)) :=
    h.of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat (ZMod 2)) (-1)).mapIso
        affineKProjectivePullbackObjectIso).symm
  exact hQ.of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat (ZMod 2)) (-1)).symm.app
      baseChangedResolution)

/-- The bounded-above-projective representative after affine base change has nonzero `H^{-1}`. -/
theorem supportedAffineBoundedAboveProjectiveRepresentative_homology_negOne_not_isZero :
    ¬ IsZero (supportedAffineBoundedAboveProjectiveRepresentative.obj.as.homology (-1)) := by
  change ¬ IsZero (baseChangedResolution.homology (-1))
  exact baseChangedResolution_homology_negOne_not_isZero

private abbrev torRingHom : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)

private abbrev torTargetModule : ModuleCat (ZMod 2) :=
  ModuleCat.of (ZMod 2) (ZMod 2)

private abbrev torFixedLeftModule : ModuleCat ℤ :=
  (ModuleCat.restrictScalars torRingHom).obj torTargetModule

private abbrev torDerivedModule : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 2)

private abbrev torRestriction : ModuleCat (ZMod 2) ⥤ ModuleCat ℤ :=
  ModuleCat.restrictScalars torRingHom

private abbrev torTensor : ModuleCat ℤ ⥤ ModuleCat ℤ :=
  (tensoringLeft (ModuleCat ℤ)).obj torFixedLeftModule

private abbrev torResolutionComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  twoTermResolution.restriction ComplexShape.embeddingDownNat

private noncomputable def torResolutionAugmentationAtZero :
    torResolutionComplex.X 0 ⟶ torDerivedModule :=
  (twoTermResolution.restrictionXIso ComplexShape.embeddingDownNat (by simp)).hom ≫
    twoTermAugmentation.f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 torDerivedModule).hom

private noncomputable def torResolutionAugmentation :
    torResolutionComplex ⟶ (ChainComplex.single₀ (ModuleCat ℤ)).obj torDerivedModule :=
  (ChainComplex.toSingle₀Equiv torResolutionComplex torDerivedModule).symm
    ⟨torResolutionAugmentationAtZero, by
      dsimp [torResolutionAugmentationAtZero]
      rw [twoTermResolution.restriction_d_eq ComplexShape.embeddingDownNat
        (i' := (-1 : ℤ)) (j' := (0 : ℤ)) (by norm_num) (by norm_num)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have h : twoTermResolution.d (-1) 0 ≫ twoTermAugmentation.f 0 = 0 := by
        simpa using (twoTermAugmentation.comm (-1) 0).symm
      simpa only [h, Category.comp_id, Category.id_comp, comp_zero, zero_comp]⟩

private noncomputable abbrev torAugmentationShortComplex : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (twoTermResolution.d (-1) 0) (twoTermAugmentation.f 0) (by
    have h : twoTermResolution.d (-1) 0 ≫ twoTermAugmentation.f 0 = 0 := by
      simpa using (twoTermAugmentation.comm (-1) 0).symm
    exact h)

private noncomputable abbrev torResolutionShortComplex : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (torResolutionComplex.d 1 0) (torResolutionAugmentation.f 0) (by
    rw [← torResolutionAugmentation.comm]
    exact comp_zero)

private noncomputable def torAugmentationShortComplexX₁Iso :
    torAugmentationShortComplex.X₁ ≅ torResolutionShortComplex.X₁ :=
  (twoTermResolution.restrictionXIso ComplexShape.embeddingDownNat
    (i := 1) (i' := (-1 : ℤ)) (by simp)).symm

private noncomputable def torAugmentationShortComplexX₂Iso :
    torAugmentationShortComplex.X₂ ≅ torResolutionShortComplex.X₂ :=
  (twoTermResolution.restrictionXIso ComplexShape.embeddingDownNat
    (i := 0) (i' := (0 : ℤ)) (by simp)).symm

private noncomputable def torAugmentationShortComplexX₃Iso :
    torAugmentationShortComplex.X₃ ≅ torResolutionShortComplex.X₃ :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 torDerivedModule) ≪≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 torDerivedModule).symm

private noncomputable def torAugmentationShortComplexIso :
    torAugmentationShortComplex ≅ torResolutionShortComplex :=
  ShortComplex.isoMk torAugmentationShortComplexX₁Iso torAugmentationShortComplexX₂Iso
    torAugmentationShortComplexX₃Iso (by
      dsimp [torAugmentationShortComplexX₁Iso, torAugmentationShortComplexX₂Iso,
        torAugmentationShortComplex, torResolutionShortComplex]
      rw [twoTermResolution.restriction_d_eq ComplexShape.embeddingDownNat
        (i' := (-1 : ℤ)) (j' := (0 : ℤ)) (by norm_num) (by norm_num)]
      simp) (by
      dsimp [torAugmentationShortComplexX₂Iso, torAugmentationShortComplexX₃Iso,
        torAugmentationShortComplex, torResolutionShortComplex, torResolutionAugmentation,
        torResolutionAugmentationAtZero]
      simp)

private theorem torAugmentationShortComplex_exact_epi :
    torAugmentationShortComplex.Exact ∧ Epi torAugmentationShortComplex.g := by
  letI : QuasiIso twoTermAugmentation := twoTermAugmentation_quasiIso
  have hq0 : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat ℤ) (ComplexShape.up ℤ)
        (-1) 0 1).map twoTermAugmentation) := by
    rw [← quasiIsoAt_iff' twoTermAugmentation (-1) 0 1 (by simp) (by simp)]
    exact QuasiIso.quasiIsoAt 0
  have hK01 : twoTermResolution.d 0 1 = 0 :=
    (twoTermResolution.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  have hTneg :
      ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.up ℤ) 0).obj torDerivedModule).d
        (-1) 0 = 0 := by simp
  have hTpos :
      ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.up ℤ) 0).obj torDerivedModule).d
        0 1 = 0 := by simp
  rw [ShortComplex.quasiIso_iff_of_zeros' _ hK01 hTneg hTpos] at hq0
  exact hq0

private theorem torResolutionShortComplex_exact_epi :
    torResolutionShortComplex.Exact ∧ Epi torResolutionShortComplex.g :=
  (ShortComplex.exact_and_epi_g_iff_of_iso torAugmentationShortComplexIso).mp
    torAugmentationShortComplex_exact_epi

private theorem torResolutionAugmentation_quasiIsoAt_zero :
    QuasiIsoAt torResolutionAugmentation 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff torResolutionAugmentation]
  rw [ShortComplex.quasiIso_iff_of_zeros' _
    (torResolutionComplex.shape 0 0 (by simp))
    (by change 0 = 0; rfl)
    (((ChainComplex.single₀ (ModuleCat ℤ)).obj torDerivedModule).shape 0 0 (by simp))]
  exact torResolutionShortComplex_exact_epi

private theorem torK_exactAt_neg (m : ℕ) :
    twoTermResolution.ExactAt (-(m + 1 : ℤ)) := by
  letI : QuasiIso twoTermAugmentation := twoTermAugmentation_quasiIso
  apply (quasiIsoAt_iff_exactAt' twoTermAugmentation (-(m + 1 : ℤ))
    (HomologicalComplex.exactAt_single_obj (ComplexShape.up ℤ) 0 torDerivedModule _
      (by omega))).mp
  exact QuasiIso.quasiIsoAt _

private theorem torResolutionComplex_exactAt_succ (m : ℕ) :
    torResolutionComplex.ExactAt (m + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (HomologicalComplex.exactAt_iff_isZero_homology twoTermResolution _).mp
    (torK_exactAt_neg m) |>.of_iso (by
      exact twoTermResolution.restrictionHomologyIso ComplexShape.embeddingDownNat
        (m + 2) (m + 1) m (by simp) (by simp)
        (i' := (-(m + 2 : ℤ))) (j' := (-(m + 1 : ℤ))) (k' := (-(m : ℤ)))
        (by simp) (by simp) (by simp)
        (by simp only [CochainComplex.prev]; omega)
        (by simp only [CochainComplex.next]; omega))

private noncomputable def torProjectiveResolution :
    ProjectiveResolution torDerivedModule where
  complex := torResolutionComplex
  projective n := by
    change Projective (twoTermResolution.X (-n))
    infer_instance
  π := torResolutionAugmentation
  quasiIso := by
    rw [quasiIso_iff]
    intro n
    rcases n with _ | m
    · exact torResolutionAugmentation_quasiIsoAt_zero
    · rw [quasiIsoAt_iff_exactAt torResolutionAugmentation (m + 1)
        (torResolutionComplex_exactAt_succ m)]
      exact ChainComplex.exactAt_succ_single_obj torDerivedModule m

private abbrev torRestrictedBaseChange : CochainComplex (ModuleCat ℤ) ℤ :=
  (torRestriction.mapHomologicalComplex (ComplexShape.up ℤ)).obj baseChangedResolution

private abbrev torTensorOnResolution : ChainComplex (ModuleCat ℤ) ℕ :=
  (torTensor.mapHomologicalComplex (ComplexShape.down ℕ)).obj torResolutionComplex

private noncomputable def torTensorOnResolutionHomologyOneIsoToRestrictedBaseChangeHomologyNegOne :
    torTensorOnResolution.homology 1 ≅ torRestrictedBaseChange.homology (-1) := by
  exact torRestrictedBaseChange.restrictionHomologyIso ComplexShape.embeddingDownNat
    2 1 0 (by simp) (by simp)
    (i' := (-2 : ℤ)) (j' := (-1 : ℤ)) (k' := (0 : ℤ))
    (by simp) (by simp) (by simp)
    (by simp only [CochainComplex.prev]; omega)
    (by simp only [CochainComplex.next]; omega)

private noncomputable def torRestrictedBaseChangeHomologyNegOneIsoToRestrictedHomologyNegOne :
    torRestrictedBaseChange.homology (-1) ≅
      torRestriction.obj (baseChangedResolution.homology (-1)) :=
  (baseChangedResolution.sc (-1)).mapHomologyIso torRestriction

private noncomputable def torIsoToRestrictedHomologyNegOne :
    ((CategoryTheory.Tor (ModuleCat ℤ) 1).obj torFixedLeftModule).obj torDerivedModule ≅
      torRestriction.obj (baseChangedResolution.homology (-1)) := by
  exact (torProjectiveResolution.isoLeftDerivedObj torTensor 1) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 1).mapIso
      ((torTensor.mapHomologicalComplex (ComplexShape.down ℕ)).mapIso (eqToIso rfl)) ≪≫
    torTensorOnResolutionHomologyOneIsoToRestrictedBaseChangeHomologyNegOne ≪≫
    torRestrictedBaseChangeHomologyNegOneIsoToRestrictedHomologyNegOne

/-- The affine degree-minus-one effect, after restriction of scalars, is Mathlib's
fixed-left and derived-second-factor `Tor` for the displayed `ℤ`-modules. -/
noncomputable def torOneIsoRestrictScalarsBaseChangedResolutionHomologyNegOne :
    (ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).obj
        (baseChangedResolution.homology (-1)) ≅
      ((CategoryTheory.Tor (ModuleCat ℤ) 1).obj
        ((ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).obj
          (ModuleCat.of (ZMod 2) (ZMod 2)))).obj (ModuleCat.of ℤ (ZMod 2)) :=
  torIsoToRestrictedHomologyNegOne.symm

private theorem torRestriction_reflects_isZero {M : ModuleCat (ZMod 2)}
    (h : IsZero (torRestriction.obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply torRestriction.map_injective
  simpa using h.eq_zero_of_src (𝟙 (torRestriction.obj M))

/-- The concrete affine `Tor₁` value is nonzero. -/
theorem torOne_not_isZero :
    ¬ IsZero (((CategoryTheory.Tor (ModuleCat ℤ) 1).obj torFixedLeftModule).obj
      torDerivedModule) := by
  intro hTor
  apply baseChangedResolution_homology_negOne_not_isZero
  apply torRestriction_reflects_isZero
  exact hTor.of_iso torIsoToRestrictedHomologyNegOne.symm

end ZModTwoNonflatDerived

end

end AlgebraicGeometry.DerivedCategory.Dqc
