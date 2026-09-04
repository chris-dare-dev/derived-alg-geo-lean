/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.Triangle.PhaseOne
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Distance.Topology
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.GLTilde.Covering.SourceTopology

/-!
# The mass-triangle inequality and its recorded consequences

This file owns the public conclusions of the subadditivity chain.  It removes
the phase-one hypothesis by head--tail octahedral induction, inhabits the named
targets stated in `HeartShortExact`, and derives the unconditional topology
comparison from the conditional substrate in `Metric.Distance.Topology`.

This is the module a consumer of the milestone should import.
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
/-- Mass is subadditive for a distinguished triangle whose first object lies
in the phase-one slice.  The proof first cuts the middle object at phase zero;
the common lower tail splits off exactly from both the middle and right
objects.  It then cuts the remaining right object at phase two; the common
upper head again splits off exactly.  The residual triangle lies in the
two-cohomology window `(0, 2]`, where
`stabilityMass_triangle_le_of_obj₁_phase_one_of_amplitude` applies. -/
theorem stabilityMass_triangle_le_of_obj₁_phase_one
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) (h₁ : σ.slicing.P 1 T.obj₁) :
    (stabilityMass σ T.obj₂).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  have hAgt0 : σ.slicing.gtProp C 0 T.obj₁ :=
    σ.slicing.gtProp_of_semistable C h₁ (by norm_num)
  have hAle2 : σ.slicing.leProp C 2 T.obj₁ :=
    σ.slicing.leProp_of_semistable C h₁ (by norm_num)
  have hAshiftP : σ.slicing.P 2 (T.obj₁⟦(1 : ℤ)⟧) := by
    convert (σ.slicing.shift_int C 1 T.obj₁ 1).mp h₁ using 1
    all_goals norm_num
  have hAshiftgt0 : σ.slicing.gtProp C 0 (T.obj₁⟦(1 : ℤ)⟧) :=
    σ.slicing.gtProp_of_semistable C hAshiftP (by norm_num)
  have hAshiftle2 : σ.slicing.leProp C 2 (T.obj₁⟦(1 : ℤ)⟧) :=
    σ.slicing.leProp_of_semistable C hAshiftP le_rfl

  obtain ⟨FE⟩ := σ.slicing.hn_exists T.obj₂
  obtain ⟨Epos, Elow, GEpos, GElow, iE, qE, dE,
      hTE, hEposgt, hElowle, _hElowBound, _hEposContain⟩ :=
    CategoryTheory.Triangulated.HNFiltration.exists_split_at_cutoff C FE 0
  have hEposgtP : σ.slicing.gtProp C 0 Epos := by
    by_cases hn : GEpos.n = 0
    · exact Or.inl (GEpos.isZero_of_length_zero hn)
    · exact σ.slicing.gtProp_of_hn C GEpos 0 hEposgt
        (Nat.pos_of_ne_zero hn)
  have hElowleP : σ.slicing.leProp C 0 Elow := by
    by_cases hn : GElow.n = 0
    · exact Or.inl (GElow.isZero_of_length_zero hn)
    · exact σ.slicing.leProp_of_hn C GElow 0 hElowle
        (Nat.pos_of_ne_zero hn)
  have hfq : T.mor₁ ≫ qE = 0 :=
    σ.slicing.zero_of_gtProp_leProp_general C 0 hAgt0 hElowleP (T.mor₁ ≫ qE)
  obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₂
    (Triangle.mk iE qE dE) hTE T.mor₁ hfq
  obtain ⟨Fpos, v, w, hU⟩ := distinguished_cocone_triangle u
  let U : Triangle C := Triangle.mk u v w
  let oct := Triangulated.someOctahedron hu.symm hU hTE hT
  have hFposgt : σ.slicing.gtProp C 0 Fpos := by
    exact σ.slicing.gtProp_of_triangle C 0 hEposgtP hAshiftgt0
      (rot_of_distTriang U hU)
  have hmassE := stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
    σ iE qE dE hTE 0 hEposgtP hElowleP
  have hmassF := stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
    σ oct.triangle.mor₁ oct.triangle.mor₂ oct.triangle.mor₃
      oct.mem 0 hFposgt hElowleP
  change (stabilityMass σ T.obj₂).toReal =
    (stabilityMass σ Epos).toReal + (stabilityMass σ Elow).toReal at hmassE
  change (stabilityMass σ T.obj₃).toReal =
    (stabilityMass σ Fpos).toReal + (stabilityMass σ Elow).toReal at hmassF

  obtain ⟨FF⟩ := σ.slicing.hn_exists Fpos
  obtain ⟨Fhigh, Flow, GFhigh, GFlow, iF, qF, dF,
      hTF, hFhighgt, hFlowle, _hFlowBound, _hFhighContain⟩ :=
    CategoryTheory.Triangulated.HNFiltration.exists_split_at_cutoff C FF 2
  have hFhighgtP : σ.slicing.gtProp C 2 Fhigh := by
    by_cases hn : GFhigh.n = 0
    · exact Or.inl (GFhigh.isZero_of_length_zero hn)
    · exact σ.slicing.gtProp_of_hn C GFhigh 2 hFhighgt
        (Nat.pos_of_ne_zero hn)
  have hFlowleP : σ.slicing.leProp C 2 Flow := by
    by_cases hn : GFlow.n = 0
    · exact Or.inl (GFlow.isZero_of_length_zero hn)
    · exact σ.slicing.leProp_of_hn C GFlow 2 hFlowle
        (Nat.pos_of_ne_zero hn)
  have hiFw : iF ≫ U.mor₃ = 0 :=
    σ.slicing.zero_of_gtProp_leProp_general C 2 hFhighgtP hAshiftle2
      (iF ≫ U.mor₃)
  obtain ⟨jF, hjF⟩ := Triangle.coyoneda_exact₃ U hU iF hiFw
  obtain ⟨Eamp, pE, dAmp, hHE⟩ := distinguished_cocone_triangle jF
  let HE : Triangle C := Triangle.mk jF pE dAmp
  let octHigh := Triangulated.someOctahedron hjF.symm hHE
    (rot_of_distTriang U hU) hTF
  let Tamp : Triangle C := Triangle.mk (U.mor₁ ≫ pE)
    octHigh.m₁ octHigh.m₃
  have hTamp : Tamp ∈ distTriang C := by
    rw [rotate_distinguished_triangle]
    change Triangle.mk octHigh.m₁ octHigh.m₃
      (-((shiftFunctor C (1 : ℤ)).map (U.mor₁ ≫ pE))) ∈ distTriang C
    rw [Functor.map_comp, ← Preadditive.neg_comp]
    simpa [octHigh, HE, U] using octHigh.mem
  have hEample2 : σ.slicing.leProp C 2 Eamp := by
    exact σ.slicing.leProp_of_triangle C 2 hAle2 hFlowleP hTamp
  have hFhighgt0 : σ.slicing.gtProp C 0 Fhigh :=
    σ.slicing.gtProp_anti C (by norm_num : (0 : ℝ) ≤ 2) Fhigh hFhighgtP
  have hFhighShiftP : σ.slicing.gtProp C 0 (Fhigh⟦(1 : ℤ)⟧) := by
    have h := σ.slicing.gtProp_shift C 2 Fhigh 1 hFhighgtP
    exact σ.slicing.gtProp_anti C (by norm_num : (0 : ℝ) ≤ 3)
      (Fhigh⟦(1 : ℤ)⟧) (by
        convert h using 1
        all_goals norm_num)
  have hEampgt0 : σ.slicing.gtProp C 0 Eamp := by
    exact σ.slicing.gtProp_of_triangle C 0 hEposgtP hFhighShiftP
      (rot_of_distTriang HE hHE)
  have hFlowgt0 : σ.slicing.gtProp C 0 Flow := by
    exact σ.slicing.gtProp_of_triangle C 0 hEampgt0 hAshiftgt0
      (rot_of_distTriang Tamp hTamp)
  have hmassEpos := stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
    σ jF pE dAmp hHE 2 hFhighgtP hEample2
  have hmassFpos := stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
    σ iF qF dF hTF 2 hFhighgtP hFlowleP
  have hamp := stabilityMass_triangle_le_of_obj₁_phase_one_of_amplitude
    σ Tamp hTamp h₁ hEampgt0 hEample2 hFlowgt0 hFlowleP
  change (stabilityMass σ Epos).toReal =
    (stabilityMass σ Fhigh).toReal + (stabilityMass σ Eamp).toReal at hmassEpos
  change (stabilityMass σ Fpos).toReal =
    (stabilityMass σ Fhigh).toReal + (stabilityMass σ Flow).toReal at hmassFpos
  change (stabilityMass σ Eamp).toReal ≤
    (stabilityMass σ T.obj₁).toReal + (stabilityMass σ Flow).toReal at hamp
  linarith

set_option maxHeartbeats 3000000 in
/-- The second mass-triangle milestone: the triangle inequality whenever the
left endpoint is semistable, at an arbitrary phase.  A lifted rotation moves
that phase to one and preserves every object's HN mass. -/
theorem stabilityMassSemistableLeftTriangleInequality :
    StabilityMassSemistableLeftTriangleInequality (C := C) (v := v) := by
  intro σ T hT φ h₁
  let θ : ℝ := 1 - φ
  have hrot : (liftedRotation θ • σ).slicing.P 1 T.obj₁ := by
    change σ.slicing.P (1 - θ) T.obj₁
    convert h₁ using 1
    all_goals simp [θ]
  have h := stabilityMass_triangle_le_of_obj₁_phase_one
    (liftedRotation θ • σ) T hT hrot
  simpa using h

set_option maxHeartbeats 3000000 in
/-- Harder--Narasimhan mass is subadditive along every distinguished triangle. -/
theorem stabilityMassTriangleInequality :
    StabilityMassTriangleInequality (C := C) (v := v) :=
  stabilityMassTriangleInequality_of_semistable_obj₁
    stabilityMassSemistableLeftTriangleInequality

set_option maxHeartbeats 3000000 in
/-- Full-distance balls form a neighbourhood basis for the pre-existing
Section 6 topology.  This closes the explicit mass-triangle premise of the
topology comparison without installing a second topology or metric instance. -/
@[cites "stmt:a520a8d4f877:bridgeland2007.prop-8.1" (relation := no_claim)
        (note := "Unconditional topology comparison obtained by applying the \
existing conditional comparison to the proved HN mass-triangle theorem. The \
citation remains no_claim pending exact-head source-faithfulness review and \
owner acceptance; no topology or metric instance is installed.")]
theorem stabilityDistanceTopologyCompatible :
    StabilityDistanceTopologyCompatible (C := C) (v := v) :=
  stabilityDistanceTopologyCompatible_of_mass_triangle
    stabilityMassTriangleInequality

/-- The global distinguished-triangle inequality restricts to the heart-level
short-exact inequality. -/
theorem stabilityMassHeartShortExactInequality_of_triangle
    (htriangle : StabilityMassTriangleInequality (C := C) (v := v)) :
    StabilityMassHeartShortExactInequality (C := C) (v := v) := by
  intro σ S hS
  obtain ⟨δ, hT⟩ := heartShortExact_exists_distinguished_triangle σ S hS
  exact htriangle σ (Triangle.mk S.f.hom S.g.hom δ) hT

/-- A short exact sequence in the heart of the slicing satisfies the mass
inequality when its middle object is semistable in the ambient slicing. -/
theorem stabilityMass_heart_shortExact_le_of_obj₂_semistable
    (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory)
    (hS : S.ShortExact) {φ : ℝ} (h₂ : σ.slicing.P φ S.X₂.obj) :
    (stabilityMass σ S.X₂.obj).toReal ≤
      (stabilityMass σ S.X₁.obj).toReal +
        (stabilityMass σ S.X₃.obj).toReal := by
  obtain ⟨δ, hT⟩ := heartShortExact_exists_distinguished_triangle σ S hS
  exact stabilityMass_triangle_le_of_obj₂_semistable σ
    (Triangle.mk S.f.hom S.g.hom δ) hT h₂

/-- A short exact sequence in the heart satisfies the mass inequality when
its endpoint objects are semistable of the same phase. -/
theorem stabilityMass_heart_shortExact_le_of_same_phase
    (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory)
    (hS : S.ShortExact) (φ : ℝ)
    (h₁ : σ.slicing.P φ S.X₁.obj) (h₃ : σ.slicing.P φ S.X₃.obj) :
    (stabilityMass σ S.X₂.obj).toReal ≤
      (stabilityMass σ S.X₁.obj).toReal +
        (stabilityMass σ S.X₃.obj).toReal := by
  obtain ⟨δ, hT⟩ := heartShortExact_exists_distinguished_triangle σ S hS
  exact stabilityMass_triangle_le_of_same_phase σ
    (Triangle.mk S.f.hom S.g.hom δ) hT φ h₁ h₃

end

end CategoryTheory.Triangulated
