/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Metric.Mass.Subadditivity.Triangle.MassAdditivity
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Metric.Mass.Subadditivity.Triangle.HeartShortExact
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Metric.Mass.Subadditivity.CohomologyExactness

/-!
# The phase-one left endpoint through the six-term cohomology sequence

This file owns the analytically expensive step of the subadditivity chain: the
comparison for a distinguished triangle whose left endpoint lies in `P(1)`.
The argument runs the six-term `H⁰` sequence, first at the level of the shifted
homological functor and then transported along the canonical `heartCoh`
identifications, and reduces a bounded-amplitude object to that window.

It is isolated because its elaboration cost dominates the module; consumers
that need only the final inequalities import `Consequences`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated Complex
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction Matrix
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition
open scoped ENNReal BigOperators ZeroObject

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

set_option maxHeartbeats 3000000 in
/-- The six-term comparison at the level of the shifted homological functor.
Keeping this categorical construction separate from the canonical
`heartCoh` identifications substantially reduces elaboration cost for the
public cohomology comparison below. -/
theorem stabilityMass_H0FunctorShift_negOne_zero_triangle_le_of_obj₁_phase_one
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C)
    (h₁ : σ.slicing.P 1 T.obj₁) :
    (stabilityMass σ
      (((CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor
        σ.slicing.toTStructure 0).shift (-1)).obj T.obj₂).obj).toReal +
      (stabilityMass σ
        (((CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor
          σ.slicing.toTStructure 0).shift (0 : ℤ)).obj T.obj₂).obj).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        ((stabilityMass σ
          (((CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor
            σ.slicing.toTStructure 0).shift (-1)).obj T.obj₃).obj).toReal +
          (stabilityMass σ
            (((CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor
              σ.slicing.toTStructure 0).shift (0 : ℤ)).obj T.obj₃).obj).toReal) := by
  let t := σ.slicing.toTStructure
  let H := CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor t 0
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : Functor.IsHomological H := by
    dsimp [H]
    infer_instance
  have hAheart : t.heart T.obj₁ := by
    dsimp [t]
    rw [σ.slicing.toTStructure_heart_iff C]
    exact ⟨σ.slicing.gtProp_of_semistable C h₁ (by norm_num),
      σ.slicing.leProp_of_semistable C h₁ le_rfl⟩
  let AH : t.heart.FullSubcategory := ⟨T.obj₁, hAheart⟩
  let Em : t.heart.FullSubcategory := (H.shift (-1)).obj T.obj₂
  let Fm : t.heart.FullSubcategory := (H.shift (-1)).obj T.obj₃
  let A0 : t.heart.FullSubcategory := (H.shift (0 : ℤ)).obj T.obj₁
  let E0 : t.heart.FullSubcategory := (H.shift (0 : ℤ)).obj T.obj₂
  let F0 : t.heart.FullSubcategory := (H.shift (0 : ℤ)).obj T.obj₃
  let gNeg : Em ⟶ Fm := (H.shift (-1)).map T.mor₂
  let δNeg : Fm ⟶ A0 := H.homologySequenceδ T (-1) (0 : ℤ) (by omega)
  let f0 : A0 ⟶ E0 := (H.shift (0 : ℤ)).map T.mor₁
  let g0 : E0 ⟶ F0 := (H.shift (0 : ℤ)).map T.mor₂

  let eA0 : A0 ≅ AH :=
    CategoryTheory.Triangulated.Tilting.originalHeartCohShiftIso t 0 T.obj₁ ≪≫
      CategoryTheory.Triangulated.Tilting.originalHeartCohIsoOfHeart t AH
  have hA0P : σ.slicing.P 1 A0.obj :=
    (σ.slicing.P 1).prop_of_iso ((t.heart).ι.mapIso eA0).symm h₁

  have hAminusZero : IsZero ((H.shift (-1)).obj T.obj₁) := by
    exact CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor_shift_isZero_of_isGE
      t ⟨hAheart.2⟩ (by omega)
  have hfNegZero : (H.shift (-1)).map T.mor₁ = 0 :=
    hAminusZero.eq_of_src _ 0
  letI : Mono gNeg :=
    (H.homologySequence_exact₂ T hT (-1)).mono_g hfNegZero
  have hgNegδ : gNeg ≫ δNeg = 0 := by
    simpa [gNeg, δNeg] using
      H.comp_homologySequenceδ T hT (-1) (0 : ℤ) (by omega)
  let K : t.heart.FullSubcategory := Abelian.image δNeg
  let qNeg : Fm ⟶ K := Abelian.factorThruImage δNeg
  have hgqNeg : gNeg ≫ qNeg = 0 := by
    rw [← cancel_mono (Abelian.image.ι δNeg), Category.assoc,
      Abelian.image.fac, hgNegδ, zero_comp]
  let Sneg : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk gNeg qNeg hgqNeg
  let SnegWide : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk gNeg δNeg hgNegδ
  have hSnegWide : SnegWide.Exact := by
    simpa [SnegWide, gNeg, δNeg] using
      H.homologySequence_exact₃ T hT (-1) (0 : ℤ) (by omega)
  let SnegCoimage : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk gNeg (Abelian.coimage.π δNeg)
      (Abelian.comp_coimage_π_eq_zero hgNegδ)
  have hSnegCoimage : SnegCoimage.Exact := by
    simpa [SnegCoimage, SnegWide] using
      (SnegWide.exact_iff_exact_coimage_π).mp hSnegWide
  have hcoimageImage : Abelian.coimage.π δNeg ≫
      (Abelian.coimageIsoImage δNeg).hom = qNeg := by
    rw [← cancel_mono (Abelian.image.ι δNeg)]
    simp [qNeg]
  let Ψneg : SnegCoimage ⟶ Sneg := ShortComplex.homMk
    (𝟙 _) (𝟙 _) (Abelian.coimageIsoImage δNeg).hom
      (by simp [SnegCoimage, Sneg])
      (by simpa [SnegCoimage, Sneg] using hcoimageImage.symm)
  letI : Epi Ψneg.τ₁ := by
    dsimp [Ψneg]
    infer_instance
  letI : IsIso Ψneg.τ₂ := by
    dsimp [Ψneg]
    infer_instance
  letI : Mono Ψneg.τ₃ := by
    dsimp [Ψneg]
    infer_instance
  have hSnegExact : Sneg.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono Ψneg).mp hSnegCoimage
  have hSneg : Sneg.ShortExact := by
    exact ShortComplex.ShortExact.mk hSnegExact

  have hf0g0 : f0 ≫ g0 = 0 := by
    simpa [f0, g0] using H.homologySequence_comp T hT (0 : ℤ)
  let I : t.heart.FullSubcategory := Abelian.image f0
  let i0 : I ⟶ E0 := Abelian.image.ι f0
  let S0 : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk i0 g0 (Abelian.image_ι_comp_eq_zero hf0g0)
  let S0wide : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk f0 g0 hf0g0
  have hS0wide : S0wide.Exact := by
    simpa [S0wide, f0, g0] using
      H.homologySequence_exact₂ T hT (0 : ℤ)
  have hS0Exact : S0.Exact := by
    simpa [S0, S0wide, i0] using
      (S0wide.exact_iff_exact_image_ι).mp hS0wide
  have hAoneZero : IsZero ((H.shift (1 : ℤ)).obj T.obj₁) := by
    exact CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor_shift_isZero_of_isLE
      t ⟨hAheart.1⟩ (by omega)
  have hδ0Zero : H.homologySequenceδ T (0 : ℤ) (1 : ℤ) (by omega) = 0 :=
    hAoneZero.eq_of_tgt _ 0
  letI : Epi g0 :=
    (H.homologySequence_exact₃ T hT (0 : ℤ) (1 : ℤ) (by omega)).epi_f hδ0Zero
  have hS0 : S0.ShortExact := by
    exact ShortComplex.ShortExact.mk hS0Exact

  have hδf0 : δNeg ≫ f0 = 0 := by
    simpa [δNeg, f0] using
      H.homologySequenceδ_comp T hT (-1) (0 : ℤ) (by omega)
  let p0 : A0 ⟶ I := by
    simpa only [I] using Abelian.factorThruImage f0
  have hKp0 : Abelian.image.ι δNeg ≫ p0 = 0 := by
    rw [← cancel_mono (Abelian.image.ι f0), Category.assoc]
    dsimp [p0]
    rw [Abelian.image.fac, zero_comp]
    exact Abelian.image_ι_comp_eq_zero hδf0
  letI : Epi p0 := by
    dsimp [p0]
    infer_instance
  let SA : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk (Abelian.image.ι δNeg) p0 hKp0
  let SAwide : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk (Abelian.image.ι δNeg) f0
      (Abelian.image_ι_comp_eq_zero hδf0)
  let Slong : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk δNeg f0 hδf0
  have hSlong : Slong.Exact := by
    simpa [Slong, δNeg, f0] using
      H.homologySequence_exact₁ T hT (-1) (0 : ℤ) (by omega)
  have hSAwide : SAwide.Exact := by
    simpa [SAwide, Slong] using (Slong.exact_iff_exact_image_ι).mp hSlong
  let Φ : SA ⟶ SAwide := ShortComplex.homMk
    (𝟙 _) (𝟙 _) (Abelian.image.ι f0)
      (by simp [SA, SAwide]) (by simp [SA, SAwide, p0])
  letI : Epi Φ.τ₁ := by
    dsimp [Φ]
    infer_instance
  letI : IsIso Φ.τ₂ := by
    dsimp [Φ]
    infer_instance
  letI : Mono Φ.τ₃ := by
    dsimp [Φ]
    infer_instance
  have hSAexact : SA.Exact := by
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono Φ).mpr hSAwide
  have hSA : SA.ShortExact := by
    exact ShortComplex.ShortExact.mk hSAexact

  obtain ⟨δA, hTA⟩ := heartShortExact_exists_distinguished_triangle σ SA hSA
  let TA : Triangle C := Triangle.mk SA.f.hom SA.g.hom δA
  have hKI : σ.slicing.P 1 K.obj ∧ σ.slicing.P 1 I.obj :=
    phaseOne_endpoints_of_heart_shortExact σ SA hSA hA0P

  have hNeg : (stabilityMass σ Em.obj).toReal ≤
      (stabilityMass σ Fm.obj).toReal +
        (stabilityMass σ K.obj).toReal := by
    exact stabilityMassBoundaryHeartInequality σ Sneg hSneg hKI.1
  obtain ⟨δ₀, hT₀⟩ := heartShortExact_exists_distinguished_triangle σ S0 hS0
  let T₀ : Triangle C := Triangle.mk S0.f.hom S0.g.hom δ₀
  have hF0le : σ.slicing.leProp C 1 F0.obj :=
    ((σ.slicing.toTStructure_heart_iff C F0.obj).mp F0.property).2
  have hZero : (stabilityMass σ E0.obj).toReal ≤
      (stabilityMass σ I.obj).toReal +
        (stabilityMass σ F0.obj).toReal := by
    simpa [T₀, S0] using
      stabilityMass_triangle_le_of_obj₁_phase_one_of_obj₃_le_one
        σ T₀ hT₀ hKI.2 hF0le
  have hAeq : (stabilityMass σ A0.obj).toReal =
      (stabilityMass σ K.obj).toReal +
        (stabilityMass σ I.obj).toReal := by
    simpa [TA, SA] using stabilityMass_toReal_triangle_eq_add_of_same_phase
      σ TA hTA 1 hKI.1 hKI.2

  have hA0Mass := stabilityMass_congr σ ((t.heart).ι.mapIso eA0)
  change stabilityMass σ A0.obj = stabilityMass σ T.obj₁ at hA0Mass
  rw [hA0Mass] at hAeq
  change (stabilityMass σ Em.obj).toReal +
      (stabilityMass σ E0.obj).toReal ≤
    (stabilityMass σ T.obj₁).toReal +
      ((stabilityMass σ Fm.obj).toReal +
        (stabilityMass σ F0.obj).toReal)
  linarith only [hNeg, hZero, hAeq]

set_option maxHeartbeats 3000000 in
/-- The six-term cohomology comparison for a phase-one source.  This is the
homological core of the semistable-left argument, stated before the ambient
objects are reassembled from their two nonzero cohomology degrees. -/
theorem stabilityMass_heartCoh_negOne_zero_triangle_le_of_obj₁_phase_one
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C)
    (h₁ : σ.slicing.P 1 T.obj₁) :
    (stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh
        σ.slicing.toTStructure (-1) T.obj₂).obj).toReal +
      (stabilityMass σ
        (CategoryTheory.Triangulated.Tilting.originalHeartCoh
          σ.slicing.toTStructure 0 T.obj₂).obj).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        ((stabilityMass σ
          (CategoryTheory.Triangulated.Tilting.originalHeartCoh
            σ.slicing.toTStructure (-1) T.obj₃).obj).toReal +
          (stabilityMass σ
            (CategoryTheory.Triangulated.Tilting.originalHeartCoh
              σ.slicing.toTStructure 0 T.obj₃).obj).toReal) := by
  let t := σ.slicing.toTStructure
  let H := CategoryTheory.Triangulated.Tilting.originalHeartCohFunctor t 0
  have hshift :=
    stabilityMass_H0FunctorShift_negOne_zero_triangle_le_of_obj₁_phase_one
      σ T hT h₁
  let eEm := CategoryTheory.Triangulated.Tilting.originalHeartCohShiftIso t (-1) T.obj₂
  let eE0 := CategoryTheory.Triangulated.Tilting.originalHeartCohShiftIso t 0 T.obj₂
  let eFm := CategoryTheory.Triangulated.Tilting.originalHeartCohShiftIso t (-1) T.obj₃
  let eF0 := CategoryTheory.Triangulated.Tilting.originalHeartCohShiftIso t 0 T.obj₃
  have hEmMass := stabilityMass_congr σ ((t.heart).ι.mapIso eEm)
  have hE0Mass := stabilityMass_congr σ ((t.heart).ι.mapIso eE0)
  have hFmMass := stabilityMass_congr σ ((t.heart).ι.mapIso eFm)
  have hF0Mass := stabilityMass_congr σ ((t.heart).ι.mapIso eF0)
  change stabilityMass σ (H.shift (-1) |>.obj T.obj₂).obj =
    stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh t (-1) T.obj₂).obj at hEmMass
  change stabilityMass σ (H.shift (0 : ℤ) |>.obj T.obj₂).obj =
    stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh t 0 T.obj₂).obj at hE0Mass
  change stabilityMass σ (H.shift (-1) |>.obj T.obj₃).obj =
    stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh t (-1) T.obj₃).obj at hFmMass
  change stabilityMass σ (H.shift (0 : ℤ) |>.obj T.obj₃).obj =
    stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh t 0 T.obj₃).obj at hF0Mass
  rw [hEmMass, hE0Mass, hFmMass, hF0Mass] at hshift
  exact hshift

set_option maxHeartbeats 3000000 in
/-- The semistable-left comparison on the two-cohomology window `(0, 2]`.
After rotating the semistable source to phase one, the unconditional
homological `H⁰` functor gives the six-term exact sequence

`0 ⟶ H⁻¹(E) ⟶ H⁻¹(F) ⟶ H⁰(A) ⟶ H⁰(E) ⟶ H⁰(F) ⟶ 0`.

Its image factorisations give short exact sequences with the common
phase-one kernel/image decomposition of `H⁰(A)`.  The negative-degree
sequence is controlled by the boundary-heart polygon inequality, the
degree-zero sequence by the phase-one extension comparison, and exact
same-ray additivity reassembles the source mass. -/
theorem stabilityMass_triangle_le_of_obj₁_phase_one_of_amplitude
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C)
    (h₁ : σ.slicing.P 1 T.obj₁)
    (hEgt : σ.slicing.gtProp C 0 T.obj₂)
    (hEle : σ.slicing.leProp C 2 T.obj₂)
    (hFgt : σ.slicing.gtProp C 0 T.obj₃)
    (hFle : σ.slicing.leProp C 2 T.obj₃) :
    (stabilityMass σ T.obj₂).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  have hEamp := stabilityMass_toReal_eq_heartCoh_negOne_add_zero
    σ T.obj₂ hEgt hEle
  have hFamp := stabilityMass_toReal_eq_heartCoh_negOne_add_zero
    σ T.obj₃ hFgt hFle
  have hcoh := stabilityMass_heartCoh_negOne_zero_triangle_le_of_obj₁_phase_one
    σ T hT h₁
  linarith only [hEamp, hFamp, hcoh]

end

end CategoryTheory.Triangulated
