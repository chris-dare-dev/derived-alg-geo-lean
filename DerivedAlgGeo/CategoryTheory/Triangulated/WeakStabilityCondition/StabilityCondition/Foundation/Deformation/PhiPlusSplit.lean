/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.BoundaryTransport
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.PullbackCokernel

/-!
# Highest-phase split for owner deformation HN recursion

When an interval object's highest old phase lies above its skewed phase by
more than the deformation tolerance, its old HN filtration supplies a
proper strict subobject of larger skewed phase.  This is the second branch
of Bridgeland's maximal-destabilizing-quotient recursion.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated

open Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace StabilityCondition.WithClassMap

/-- If `φ⁺(Y) > ψ(Y) + ε`, splitting the old HN filtration at
`ψ(Y) + ε` produces a proper strict subobject whose skewed phase is larger
than that of `Y`.  The subobject also retains the closed lower phase cut
used for the MDQ minimality argument. -/
theorem exists_strictSubobject_of_phiPlus_gt
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {L U : ℝ}
    (hWindow : ∀ Z : σ.slicing.IntervalCat C a b, ¬IsZero Z.obj →
      L < (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase Z.obj ∧
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase Z.obj < U)
    (hWidth : U - L < 1)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hL_a : a ≤ L + ε)
    {Y : σ.slicing.IntervalCat C a b} (hY : ¬IsZero Y.obj)
    (hplus :
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase Y.obj + ε <
        σ.slicing.phiPlus C Y.obj hY) :
    ∃ A : Subobject Y,
      A ≠ ⊥ ∧ A ≠ ⊤ ∧ IsStrictMono A.arrow ∧
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase Y.obj <
        (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase
          (A : σ.slicing.IntervalCat C a b).obj ∧
      σ.slicing.geProp C
        ((skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase Y.obj + ε)
        (A : σ.slicing.IntervalCat C a b).obj := by
  let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
  let ψY := F.phase Y.obj
  have hYI : ¬IsZero Y := fun h => hY ((σ.slicing.intervalProp C a b).ι.map_isZero h)
  rcases Y.property with hYZ | ⟨G, hG⟩
  · exact (hY hYZ).elim
  · obtain ⟨Xhi, Ylo, f, g, δ, hT, hXgt, hYle, hXlt⟩ :=
      σ.slicing.exists_split_at_cutoff C G hG (t := ψY + ε)
    have hXhi : ¬IsZero Xhi := by
      intro hXzero
      haveI : IsIso g :=
        (Triangle.isZero₁_iff_isIso₂ (Triangle.mk f g δ) hT).mp hXzero
      let e : Y.obj ≅ Ylo := asIso g
      have hYle' : σ.slicing.leProp C (ψY + ε) Y.obj := by
        rcases hYle with hzero | ⟨GY, hn, hle⟩
        · exact Or.inl (hzero.of_iso e)
        · exact Or.inr ⟨GY.ofIso C e.symm, hn, hle⟩
      have := σ.slicing.phiPlus_le_of_leProp C hY hYle'
      linarith
    have ht_b : ψY + ε < b := by
      have hminus := σ.slicing.phiMinus_gt_of_gtProp C hXhi hXgt
      have hupper := σ.slicing.phiPlus_lt_of_ltProp C hXhi hXlt
      linarith [σ.slicing.phiMinus_le_phiPlus C Xhi hXhi]
    have hXint : σ.slicing.intervalProp C a b Xhi :=
      σ.slicing.intervalProp_of_intrinsic_phases C hXhi
        (by
          have hminus := σ.slicing.phiMinus_gt_of_gtProp C hXhi hXgt
          have hYwindow := hWindow Y hY
          dsimp [ψY] at hminus
          linarith [hL_a, hYwindow.1])
        (σ.slicing.phiPlus_lt_of_ltProp C hXhi hXlt)
    have hYloLt : σ.slicing.ltProp C b Ylo := by
      rcases hYle with hzero | ⟨GY, hn, hle⟩
      · exact Or.inl hzero
      · exact Or.inr ⟨GY, hn, hle.trans_lt ht_b⟩
    have hXge : σ.slicing.geProp C (b - 1) Xhi := by
      apply σ.slicing.geProp_of_gtProp
      apply σ.slicing.gtProp_anti C (t₂ := ψY + ε)
      · have hYwindow := hWindow Y hY
        dsimp [ψY]
        linarith [Fact.out (p := b - a ≤ 1), hL_a, hYwindow.1]
      · exact hXgt
    have hYloInt : σ.slicing.intervalProp C a b Ylo :=
      σ.slicing.third_intervalProp_of_triangle C hab Y.property hXge hYloLt hT
    let XhiI : σ.slicing.IntervalCat C a b := ⟨Xhi, hXint⟩
    let YloI : σ.slicing.IntervalCat C a b := ⟨Ylo, hYloInt⟩
    let fI : XhiI ⟶ Y := ObjectProperty.homMk f
    let gI : Y ⟶ YloI := ObjectProperty.homMk g
    let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
      ShortComplex.mk fI gI (by
        apply ObjectProperty.hom_ext
        exact comp_distTriang_mor_zero₁₂ _ hT)
    have hS : StrictShortExact S :=
      Slicing.IntervalCat.strictShortExact_of_distinguished C σ.slicing hT
    have hf : IsStrictMono fI := ⟨hS.shortExact.mono_f, hS.strict_f⟩
    letI : Mono fI := hf.mono
    let A : Subobject Y := Subobject.mk fI
    have hAstrict : IsStrictMono A.arrow := by
      simpa [A] using Slicing.IntervalCat.subobject_arrow_strictMono C fI hf
    let eA : (A : σ.slicing.IntervalCat C a b) ≅ XhiI :=
      Subobject.isoOfEqMk A fI rfl
    have hAne : A ≠ ⊥ := by
      intro hbot
      have hAzero : IsZero (A : σ.slicing.IntervalCat C a b) :=
        (Slicing.IntervalCat.subobject_isZero_iff_eq_bot (C := C) A).2 hbot
      exact hXhi ((σ.slicing.intervalProp C a b).ι.map_isZero
        (hAzero.of_iso eA.symm))
    have hbranch : b + ε < ψY + 1 := by
      have hYwindow := hWindow Y hY
      dsimp [ψY]
      linarith [hthin, hL_a, hYwindow.1]
    have hAtop : A ≠ ⊤ := by
      intro htop
      haveI : IsIso fI := (Subobject.isIso_iff_mk_eq_top fI).2 htop
      have hYge : σ.slicing.geProp C (ψY + ε) Y.obj :=
        (σ.slicing.geProp C (ψY + ε)).prop_of_iso
          ((σ.slicing.intervalProp C a b).ι.mapIso (asIso fI))
          (σ.slicing.geProp_of_gtProp C Xhi hXgt)
      have hcontra := σ.skewedPhase_gt_of_geProp_of_phase_range C W hr0 hr1 hW
        hab hε hε2 hthin hsin Y.property hY
        (show F.phase Y.obj ∈ Set.Ioo (ψY - 1) (ψY + 1) by
          dsimp [ψY]; constructor <;> linarith)
        hbranch hYge
      exact (lt_irrefl ψY) (by simpa [F, ψY] using hcontra)
    have hXphase : ψY < F.phase Xhi := by
      have hXwindow := hWindow XhiI hXhi
      have hYwindow := hWindow Y hY
      apply σ.skewedPhase_gt_of_geProp_of_phase_range C W hr0 hr1 hW
        hab hε hε2 hthin hsin hXint hXhi
      · change F.phase Xhi ∈ Set.Ioo (ψY - 1) (ψY + 1)
        constructor <;> linarith [hWidth, hXwindow.1, hXwindow.2,
          hYwindow.1, hYwindow.2]
      · exact hbranch
      · exact σ.slicing.geProp_of_gtProp C Xhi hXgt
    have hAphase : ψY < F.phase (A : σ.slicing.IntervalCat C a b).obj := by
      let eC : (A : σ.slicing.IntervalCat C a b).obj ≅ Xhi :=
        (σ.slicing.intervalProp C a b).ι.mapIso eA
      rw [F.phase_iso eC]
      exact hXphase
    have hAge : σ.slicing.geProp C (ψY + ε)
        (A : σ.slicing.IntervalCat C a b).obj :=
      (σ.slicing.geProp C (ψY + ε)).prop_of_iso
        ((σ.slicing.intervalProp C a b).ι.mapIso eA).symm
        (σ.slicing.geProp_of_gtProp C Xhi hXgt)
    exact ⟨A, hAne, hAtop, hAstrict, hAphase, hAge⟩

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
