/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.PhiPlusReduction
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.PhiPlusSplit

/-!
# Owner maximal destabilizing quotients for deformation

This is the two-branch MDQ recursion in Bridgeland's deformation argument.
The controlled `φ⁺` branch uses the sharp deformed Hom-vanishing theorem;
the complementary branch splits the old HN filtration at `ψ + ε`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace StabilityCondition.WithClassMap

/-- A nonzero thin-interval object admits a strict MDQ while all semistable
strict quotients are constrained above a common lower phase cutoff. -/
theorem exists_strictMDQ_with_quotient_bound
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFinite : ThinStrictFiniteLength C σ a b)
    {L U : ℝ}
    (hWindow : ∀ Y : σ.slicing.IntervalCat C a b, ¬IsZero Y.obj →
      L < (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase Y.obj ∧
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase Y.obj < U)
    (hWidth : U - L < 1)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hL_a : a ≤ L + ε)
    {t : ℝ} (ht : a + ε ≤ t)
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hQuotLo : ∀ {B' : σ.slicing.IntervalCat C a b} (q' : X ⟶ B'),
      IsStrictEpi q' → ¬IsZero B'.obj →
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).IsSemistable
        B'.obj
        ((skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase B'.obj) →
      t < (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase B'.obj)
    (hXupper :
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase X.obj <
        b - 3 * ε) :
    ∃ (B : σ.slicing.IntervalCat C a b) (q : X ⟶ B),
      IsStrictMDQ C σ
        (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab) q := by
  let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
  have hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E := by
    intro E hI hE
    exact σ.charge_ne_of_interval C W hr0 hr1 hW hab hε hε2
      hthin hsin hI hE
  letI : IsStrictNoetherianObject X := (hFinite X).2
  suffices h : ∀ S : StrictSubobject X,
      ¬IsZero (cokernel S.1.arrow) →
      F.phase (cokernel S.1.arrow).obj < b - 3 * ε →
      (∀ {B' : σ.slicing.IntervalCat C a b}
        (q' : cokernel S.1.arrow ⟶ B'), IsStrictEpi q' →
        ¬IsZero B'.obj → F.IsSemistable B'.obj (F.phase B'.obj) →
        t < F.phase B'.obj) →
      ∃ (B : σ.slicing.IntervalCat C a b)
        (q : cokernel S.1.arrow ⟶ B), IsStrictMDQ C σ F q by
    let S0 : StrictSubobject X :=
      ⟨⊥, Slicing.IntervalCat.bot_arrow_strictMono C⟩
    let e0 : cokernel S0.1.arrow ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
      exact cokernelZeroIsoTarget
    have hS0 : ¬IsZero (cokernel S0.1.arrow) := fun hzero =>
      hX (hzero.of_iso e0.symm)
    have hQLo0 : ∀ {B' : σ.slicing.IntervalCat C a b}
        (q' : cokernel S0.1.arrow ⟶ B'), IsStrictEpi q' →
        ¬IsZero B'.obj → F.IsSemistable B'.obj (F.phase B'.obj) →
        t < F.phase B'.obj := by
      intro B' q' hq' hB' hB'ss
      exact hQuotLo (e0.inv ≫ q')
        (Slicing.IntervalCat.comp_strictEpi C σ.slicing e0.inv q'
          isStrictEpi_of_isIso hq') hB' hB'ss
    have hupper0 : F.phase (cokernel S0.1.arrow).obj < b - 3 * ε := by
      let eC : (cokernel S0.1.arrow).obj ≅ X.obj :=
        (σ.slicing.intervalProp C a b).ι.mapIso e0
      rw [F.phase_iso eC]
      exact hXupper
    obtain ⟨B, q, hq⟩ := h S0 hS0 hupper0 hQLo0
    exact ⟨B, e0.inv ≫ q, IsStrictMDQ.precomposeIso C hq e0.symm⟩
  intro S
  induction S using IsWellFounded.induction
      (· > · : StrictSubobject X → StrictSubobject X → Prop) with
  | ind S ih =>
      intro hQS hQSupper hQLoS
      let QS : σ.slicing.IntervalCat C a b := cokernel S.1.arrow
      letI : IsStrictArtinianObject QS := (hFinite QS).1
      letI : IsStrictNoetherianObject QS := (hFinite QS).2
      have hQSobj : ¬IsZero QS.obj := fun hzero =>
        hQS (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hzero)
      by_cases hQSss : F.IsSemistable QS.obj (F.phase QS.obj)
      · exact ⟨QS, 𝟙 _, IsStrictMDQ.id_of_semistable C
          hWindow hWidth hQSss⟩
      · by_cases hplus :
          σ.slicing.phiPlus C QS.obj hQSobj ≤ F.phase QS.obj + ε
        · obtain ⟨A, hAne, hAtop, hAstrict, hAss, hAphase, _⟩ :=
            F.exists_first_strictShortExact_of_not_semistable C
              (X := QS) hQS hQSss hCharge
          have hAupper : F.phase (A : σ.slicing.IntervalCat C a b).obj <
              b - ε :=
            σ.phase_lt_upper_of_destabilizing_subobject C W hr0 hr1 hW
              hab hε hε2 hthin hsin hQSobj hplus hQSupper hAss hAstrict
          let Tsub : Subobject X :=
            (Subobject.pullback (cokernel.π S.1.arrow)).obj A
          have hTstrict : IsStrictMono Tsub.arrow :=
            Slicing.IntervalCat.pullbackArrow_strictMono C
              (cokernel.π S.1.arrow) A hAstrict
          let T : StrictSubobject X := ⟨Tsub, hTstrict⟩
          have hST : S < T :=
            Slicing.IntervalCat.lt_pullbackCokernel_of_ne_bot C hAne
          have hTtop : Tsub ≠ ⊤ :=
            Slicing.IntervalCat.pullbackCokernel_ne_top C hAtop hAstrict
          have hQT : ¬IsZero (cokernel Tsub.arrow) :=
            Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hTtop hTstrict
          let eT : cokernel Tsub.arrow ≅ cokernel A.arrow :=
            Slicing.IntervalCat.cokernelPullbackIso C S.1 hAstrict
          have hQLoT : ∀ {B' : σ.slicing.IntervalCat C a b}
              (q' : cokernel Tsub.arrow ⟶ B'), IsStrictEpi q' →
              ¬IsZero B'.obj → F.IsSemistable B'.obj (F.phase B'.obj) →
              t < F.phase B'.obj := by
            intro B' q' hq' hB' hB'ss
            exact hQLoS (cokernel.π A.arrow ≫ eT.inv ≫ q')
              (Slicing.IntervalCat.comp_strictEpi C σ.slicing
                (cokernel.π A.arrow) (eT.inv ≫ q')
                (isStrictEpi_cokernel A.arrow)
                (Slicing.IntervalCat.comp_strictEpi C σ.slicing eT.inv q'
                  isStrictEpi_of_isIso hq')) hB' hB'ss
          have hCokLt : F.phase (cokernel A.arrow).obj < F.phase QS.obj :=
            F.phase_cokernel_lt_of_phase_gt_strictSubobject C hAne hAtop
              hAstrict hAphase hCharge hWindow hWidth
          have hTupper : F.phase (cokernel Tsub.arrow).obj < b - 3 * ε := by
            rw [F.phase_cokernelPullback C S.1 hAstrict]
            exact hCokLt.trans hQSupper
          obtain ⟨B, qT, hqT⟩ := ih T hST hQT hTupper hQLoT
          let qA : cokernel A.arrow ⟶ B := eT.inv ≫ qT
          have hqA : IsStrictMDQ C σ F qA :=
            IsStrictMDQ.precomposeIso C hqT eT.symm
          have hBlo : t < F.phase B.obj :=
            hQLoS (cokernel.π A.arrow ≫ qA)
              (Slicing.IntervalCat.comp_strictEpi C σ.slicing
                (cokernel.π A.arrow) qA
                (isStrictEpi_cokernel A.arrow) hqA.strictEpi)
              hqA.nonzero hqA.semistable
          have hCokObj : ¬IsZero (cokernel A.arrow).obj := fun hzero =>
            (Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hAtop hAstrict)
              (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hzero)
          have hBle : F.phase B.obj ≤ F.phase (cokernel A.arrow).obj :=
            hqA.phase_le_of_strictQuotient C hFinite hCharge hWindow hWidth
              (𝟙 _) isStrictEpi_of_isIso hCokObj
          have hQSlo : t < F.phase QS.obj := by linarith
          exact ⟨B, cokernel.π A.arrow ≫ qA,
            σ.comp_mdq_of_destabilizing_with_quotient_bound C W hr0 hr1 hW
              hab hFinite hWindow hWidth hε hε2 hε8 hthin hsin ht
              hQSlo hQLoS hAss hAstrict hAphase hAtop hAupper hqA⟩
        · push Not at hplus
          obtain ⟨A, hAne, hAtop, hAstrict, hAphase, hAge⟩ :=
            σ.exists_strictSubobject_of_phiPlus_gt C W hr0 hr1 hW hab
              hWindow hWidth hε hε2 hthin hsin hL_a hQSobj hplus
          let Tsub : Subobject X :=
            (Subobject.pullback (cokernel.π S.1.arrow)).obj A
          have hTstrict : IsStrictMono Tsub.arrow :=
            Slicing.IntervalCat.pullbackArrow_strictMono C
              (cokernel.π S.1.arrow) A hAstrict
          let T : StrictSubobject X := ⟨Tsub, hTstrict⟩
          have hST : S < T :=
            Slicing.IntervalCat.lt_pullbackCokernel_of_ne_bot C hAne
          have hTtop : Tsub ≠ ⊤ :=
            Slicing.IntervalCat.pullbackCokernel_ne_top C hAtop hAstrict
          have hQT : ¬IsZero (cokernel Tsub.arrow) :=
            Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hTtop hTstrict
          let eT : cokernel Tsub.arrow ≅ cokernel A.arrow :=
            Slicing.IntervalCat.cokernelPullbackIso C S.1 hAstrict
          have hQLoT : ∀ {B' : σ.slicing.IntervalCat C a b}
              (q' : cokernel Tsub.arrow ⟶ B'), IsStrictEpi q' →
              ¬IsZero B'.obj → F.IsSemistable B'.obj (F.phase B'.obj) →
              t < F.phase B'.obj := by
            intro B' q' hq' hB' hB'ss
            exact hQLoS (cokernel.π A.arrow ≫ eT.inv ≫ q')
              (Slicing.IntervalCat.comp_strictEpi C σ.slicing
                (cokernel.π A.arrow) (eT.inv ≫ q')
                (isStrictEpi_cokernel A.arrow)
                (Slicing.IntervalCat.comp_strictEpi C σ.slicing eT.inv q'
                  isStrictEpi_of_isIso hq')) hB' hB'ss
          have hCokLt : F.phase (cokernel A.arrow).obj < F.phase QS.obj :=
            F.phase_cokernel_lt_of_phase_gt_strictSubobject C hAne hAtop
              hAstrict hAphase hCharge hWindow hWidth
          have hTupper : F.phase (cokernel Tsub.arrow).obj < b - 3 * ε := by
            rw [F.phase_cokernelPullback C S.1 hAstrict]
            exact hCokLt.trans hQSupper
          obtain ⟨B, qT, hqT⟩ := ih T hST hQT hTupper hQLoT
          let qA : cokernel A.arrow ⟶ B := eT.inv ≫ qT
          have hqA : IsStrictMDQ C σ F qA :=
            IsStrictMDQ.precomposeIso C hqT eT.symm
          have hCokObj : ¬IsZero (cokernel A.arrow).obj := fun hzero =>
            (Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hAtop hAstrict)
              (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hzero)
          have hBle : F.phase B.obj ≤ F.phase (cokernel A.arrow).obj :=
            hqA.phase_le_of_strictQuotient C hFinite hCharge hWindow hWidth
              (𝟙 _) isStrictEpi_of_isIso hCokObj
          have hvanish : ∀ {B' : σ.slicing.IntervalCat C a b}
              (q' : QS ⟶ B'), F.IsSemistable B'.obj (F.phase B'.obj) →
              F.phase B'.obj ≤ F.phase B.obj → A.arrow ≫ q' = 0 := by
            intro B' q' hB'ss hle
            have hB'lt : F.phase B'.obj < F.phase QS.obj :=
              hle.trans hBle |>.trans_lt hCokLt
            have hplusB := σ.skewed_phiPlus_le C W hr0 hr1 hW hab
              hε hε2 hthin hsin hB'ss
            have hB'cut : σ.slicing.ltProp C (F.phase QS.obj + ε) B'.obj :=
              σ.slicing.ltProp_of_phiPlus_lt C hB'ss.nonzero (by linarith)
            apply ObjectProperty.hom_ext
            exact σ.slicing.zero_of_geProp_ltProp_at C
              (F.phase QS.obj + ε) hAge hB'cut (A.arrow ≫ q').hom
          refine ⟨B, cokernel.π A.arrow ≫ qA, {
            strictEpi := Slicing.IntervalCat.comp_strictEpi C σ.slicing
              (cokernel.π A.arrow) qA
              (isStrictEpi_cokernel A.arrow) hqA.strictEpi
            nonzero := hqA.nonzero
            semistable := hqA.semistable
            minimal := ?_ }⟩
          intro B' q' hq' hB' hB'ss
          by_cases hle : F.phase B.obj ≤ F.phase B'.obj
          · refine ⟨hle, ?_⟩
            intro heq
            have hzero := hvanish q' hB'ss (by rw [heq])
            let q'' : cokernel A.arrow ⟶ B' :=
              cokernel.desc A.arrow q' hzero
            have hq'' : IsStrictEpi q'' := by
              apply Slicing.IntervalCat.strictEpi_of_comp_strictEpi C σ.slicing
                (cokernel.π A.arrow) q''
              simpa [q''] using hq'
            obtain ⟨u, hu⟩ := hqA.factor_of_phase_eq C q'' hq'' hB' hB'ss heq
            exact ⟨u, by
              calc
                q' = cokernel.π A.arrow ≫ q'' :=
                  (cokernel.π_desc A.arrow q' hzero).symm
                _ = cokernel.π A.arrow ≫ (qA ≫ u) := by rw [hu]
                _ = (cokernel.π A.arrow ≫ qA) ≫ u := by
                  simp [qA, Category.assoc]⟩
          · have hlt : F.phase B'.obj < F.phase B.obj := lt_of_not_ge hle
            have hzero := hvanish q' hB'ss hlt.le
            let q'' : cokernel A.arrow ⟶ B' :=
              cokernel.desc A.arrow q' hzero
            have hq'' : IsStrictEpi q'' := by
              apply Slicing.IntervalCat.strictEpi_of_comp_strictEpi C σ.slicing
                (cokernel.π A.arrow) q''
              simpa [q''] using hq'
            exact False.elim ((not_lt_of_ge
              (hqA.phase_le C q'' hq'' hB' hB'ss)) hlt)

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
