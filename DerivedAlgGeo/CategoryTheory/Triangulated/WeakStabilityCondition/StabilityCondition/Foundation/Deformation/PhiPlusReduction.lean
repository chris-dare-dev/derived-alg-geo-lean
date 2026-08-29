/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.TargetTransport
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.FiniteLengthHN

/-!
# Highest-phase reduction for owner deformation HN recursion

This file packages the two estimates used to keep the recursive strict-MDQ
construction inside a phase-enveloping interval.  It is the owner-native
version of the `phiPlus` reduction in Bridgeland's deformation proof.
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

/-- If the highest old phase of `Y` is controlled by its skewed phase, then
every skewed-semistable strict subobject of `Y` stays below the upper
deformation boundary. -/
theorem phase_lt_upper_of_destabilizing_subobject
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε : ℝ} (hab : a < b)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {Y : σ.slicing.IntervalCat C a b} (hY : ¬IsZero Y.obj)
    (hplus : σ.slicing.phiPlus C Y.obj hY ≤
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase Y.obj + ε)
    (hupper :
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase Y.obj <
        b - 3 * ε)
    {A : Subobject Y}
    (hA : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).IsSemistable
      (A : σ.slicing.IntervalCat C a b).obj
      ((skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase
        (A : σ.slicing.IntervalCat C a b).obj))
    (hAstrict : IsStrictMono A.arrow) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase
        (A : σ.slicing.IntervalCat C a b).obj < b - ε := by
  let AI : σ.slicing.IntervalCat C a b := A
  have hS := Slicing.IntervalCat.strictShortExact_cokernel C A.arrow hAstrict
  obtain ⟨δ, hT⟩ :=
    Slicing.IntervalCat.exists_distinguished_of_strictShortExact C σ.slicing hS
  have hAle : σ.slicing.phiPlus C AI.obj hA.nonzero ≤
      σ.slicing.phiPlus C Y.obj hY :=
    σ.slicing.phiPlus_triangle_le C hA.nonzero hY (by linarith)
      AI.property (cokernel A.arrow).property hT
  have hminus := σ.skewed_phiMinus_ge C W hr0 hr1 hW hab hε hε2
    hthin hsin hA
  have hminmax := σ.slicing.phiMinus_le_phiPlus C AI.obj hA.nonzero
  linarith

/-- Sharp Hom-vanishing for two skewed-semistable objects whose phases are
enveloped by their common thin interval. -/
theorem hom_eq_zero_of_enveloped_semistable
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε : ℝ} (hab : a < b)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E F : C}
    (hE : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).IsSemistable
      E ((skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E))
    (hF : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).IsSemistable
      F ((skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase F))
    (hgap : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase F <
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E)
    (hElo : a + ε ≤
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E)
    (hEhi :
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E ≤ b - ε)
    (hFlo : a + ε ≤
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase F)
    (hFhi :
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase F ≤ b - ε)
    (f : E ⟶ F) : f = 0 := by
  have hEd : σ.deformedPred C W hr0 hr1 hW ε
      ((skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E) E :=
    Or.inr ⟨a, b, hab, hthin, hElo, hEhi, hE⟩
  have hFd : σ.deformedPred C W hr0 hr1 hW ε
      ((skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase F) F :=
    Or.inr ⟨a, b, hab, hthin, hFlo, hFhi, hF⟩
  exact σ.hom_eq_zero_of_deformedPred C W hr0 hr1 hW
    hε hε2 hε8 hsin hEd hFd hgap f

/-- Compose an MDQ across a destabilizing strict subobject when all
semistable strict quotients of the ambient object have a common lower phase
bound.  That lower bound and the highest-phase estimate put the two objects
in the enveloped range needed for sharp Hom-vanishing. -/
theorem comp_mdq_of_destabilizing_with_quotient_bound
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
    {t : ℝ} (ht : a + ε ≤ t)
    {X : σ.slicing.IntervalCat C a b}
    (hXlo : t <
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase X.obj)
    (hQuotLo : ∀ {G : σ.slicing.IntervalCat C a b} (p : X ⟶ G),
      IsStrictEpi p → ¬IsZero G.obj →
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).IsSemistable
        G.obj ((skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase G.obj) →
      t < (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase G.obj)
    {A : Subobject X}
    (hA : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).IsSemistable
      (A : σ.slicing.IntervalCat C a b).obj
      ((skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase
        (A : σ.slicing.IntervalCat C a b).obj))
    (hAstrict : IsStrictMono A.arrow)
    (hAphase :
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase X.obj <
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase
        (A : σ.slicing.IntervalCat C a b).obj)
    (hAtop : A ≠ ⊤)
    (hAupper :
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase
        (A : σ.slicing.IntervalCat C a b).obj < b - ε)
    {Q : σ.slicing.IntervalCat C a b} {q : cokernel A.arrow ⟶ Q}
    (hq : IsStrictMDQ C σ
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab) q) :
    IsStrictMDQ C σ
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab)
      (cokernel.π A.arrow ≫ q) := by
  let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
  have hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E := by
    intro E hI hE
    exact σ.charge_ne_of_interval C W hr0 hr1 hW hab hε hε2
      hthin hsin hI hE
  refine {
    strictEpi := Slicing.IntervalCat.comp_strictEpi C σ.slicing
      (cokernel.π A.arrow) q (isStrictEpi_cokernel A.arrow) hq.strictEpi
    nonzero := hq.nonzero
    semistable := hq.semistable
    minimal := ?_ }
  intro Q' p hp hQ' hQ'ss
  have hCokI : ¬IsZero (cokernel A.arrow) :=
    Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hAtop hAstrict
  have hCok : ¬IsZero (cokernel A.arrow).obj := fun h ↦
    hCokI (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
  have hQle : F.phase Q.obj ≤ F.phase (cokernel A.arrow).obj :=
    hq.phase_le_of_strictQuotient C hFinite hCharge hWindow hWidth
      (𝟙 (cokernel A.arrow)) isStrictEpi_of_isIso hCok
  have hAne : A ≠ ⊥ := by
    intro hbot
    have hAI : IsZero (A : σ.slicing.IntervalCat C a b) :=
      (Slicing.IntervalCat.subobject_isZero_iff_eq_bot C A).2 hbot
    exact hA.nonzero (((σ.slicing.intervalProp C a b).ι).map_isZero hAI)
  have hCokA : F.phase (cokernel A.arrow).obj <
      F.phase (A : σ.slicing.IntervalCat C a b).obj :=
    (F.phase_cokernel_lt_of_phase_gt_strictSubobject C hAne hAtop
      hAstrict hAphase hCharge hWindow hWidth).trans hAphase
  have hQltA : F.phase Q.obj <
      F.phase (A : σ.slicing.IntervalCat C a b).obj :=
    hQle.trans_lt hCokA
  have hvanish : F.phase Q'.obj <
      F.phase (A : σ.slicing.IntervalCat C a b).obj → A.arrow ≫ p = 0 := by
    intro hQ'lt
    apply ObjectProperty.hom_ext
    exact σ.hom_eq_zero_of_enveloped_semistable C W hr0 hr1 hW hab
      hε hε2 hε8 hthin hsin hA hQ'ss hQ'lt
      (by linarith [ht, hXlo, hAphase]) (le_of_lt hAupper)
      (by linarith [ht, hQuotLo p hp hQ' hQ'ss])
      (by linarith [hQ'lt, hAupper]) (A.arrow ≫ p).hom
  by_cases hle : F.phase Q.obj ≤ F.phase Q'.obj
  · refine ⟨hle, ?_⟩
    intro heq
    have hQ'lt : F.phase Q'.obj <
        F.phase (A : σ.slicing.IntervalCat C a b).obj := by
      rw [heq]
      exact hQltA
    have hzero := hvanish hQ'lt
    let p' : cokernel A.arrow ⟶ Q' := cokernel.desc A.arrow p hzero
    have hp' : IsStrictEpi p' := by
      apply Slicing.IntervalCat.strictEpi_of_comp_strictEpi C σ.slicing
        (cokernel.π A.arrow) p'
      simpa [p'] using hp
    obtain ⟨u, hu⟩ := hq.factor_of_phase_eq C p' hp' hQ' hQ'ss heq
    refine ⟨u, ?_⟩
    calc
      p = cokernel.π A.arrow ≫ p' :=
        (cokernel.π_desc A.arrow p hzero).symm
      _ = cokernel.π A.arrow ≫ (q ≫ u) := by rw [hu]
      _ = (cokernel.π A.arrow ≫ q) ≫ u := by rw [Category.assoc]
  · have hlt : F.phase Q'.obj < F.phase Q.obj := lt_of_not_ge hle
    have hQ'lt := hlt.trans hQltA
    have hzero := hvanish hQ'lt
    let p' : cokernel A.arrow ⟶ Q' := cokernel.desc A.arrow p hzero
    have hp' : IsStrictEpi p' := by
      apply Slicing.IntervalCat.strictEpi_of_comp_strictEpi C σ.slicing
        (cokernel.π A.arrow) p'
      simpa [p'] using hp
    exact False.elim ((not_lt_of_ge
      (hq.phase_le C p' hp' hQ' hQ'ss)) hlt)

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
