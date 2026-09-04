/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.DeformedHom
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.FirstStrictSES
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.PullbackCokernel
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Slicing.IntervalStrictness

/-!
# Target-envelope transport for owner skewed semistability

The existential interval in the owner deformed predicate is auxiliary.  This
file proves that a semistability witness can be read in every other thin old
phase interval which contains the object and envelops the recorded phase.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated.TStructure
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace Slicing.IntervalCat

variable {s : Slicing C} {a b : ℝ}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- The first map of a distinguished triangle inside a thin owner interval
is a kernel of the second map. -/
noncomputable def isLimitKernelForkOfDistinguished
    {S : ShortComplex (s.IntervalCat C a b)}
    {δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C) :
    IsLimit (KernelFork.ofι S.f S.zero) := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FL := Slicing.IntervalCat.toLeftHeart
    (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  have hL : (S.map FL).ShortExact := by
    change (ShortComplex.mk (FL.map S.f) (FL.map S.g) _).ShortExact
    exact heartFullSubcategory_shortExact_of_distTriang t hT
  have hKerL : IsLimit
      (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) := hL.fIsKernel
  have hKerMap : IsLimit
      (FL.mapCone (KernelFork.ofι S.f S.zero)) :=
    (isLimitMapConeForkEquiv' FL S.zero).symm hKerL
  exact isLimitOfReflects FL hKerMap

end Slicing.IntervalCat

namespace StabilityCondition.WithClassMap

omit [IsTriangulated C] in
/-- Repackage a source semistability proof once the target interval tests
have been discharged. -/
theorem skewedSemistable_of_target_triangleTest
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a₁ b₁ a₂ b₂ ε ψ : ℝ} (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂)
    (hε : 0 < ε)
    (hthin₂ : b₂ - a₂ + 2 * ε < 1)
    (ha₂ψ : a₂ + ε ≤ ψ) (hψb₂ : ψ ≤ b₂ - ε)
    {E : C} (hI₂ : σ.slicing.intervalProp C a₂ b₂ E)
    (hSS : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₁).IsSemistable
      E ψ)
    (htri : ∀ ⦃K Q : C⦄ ⦃i : K ⟶ E⦄ ⦃q : E ⟶ Q⦄ ⦃δ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
      Triangle.mk i q δ ∈ distTriang C →
      σ.slicing.intervalProp C a₂ b₂ K →
      σ.slicing.intervalProp C a₂ b₂ Q →
      ¬IsZero K →
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₂).phase K ≤ ψ) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₂).IsSemistable
      E ψ where
  interval := hI₂
  nonzero := hSS.nonzero
  charge_ne := hSS.charge_ne
  phase_eq := σ.skewedPhase_eq_of_target_envelope C W hr0 hr1 hW hab₁ hab₂
    hε hthin₂ ha₂ψ hψb₂ hSS
  phase_le_of_triangle := htri

omit [IsTriangulated C] in
/-- If two summands have phases at most `ψ`, one strictly so, their sum has
phase strictly below `ψ`, provided all selected phases use the same branch. -/
theorem phase_add_lt_of_le_of_lt
    {s : Slicing C} {a b : ℝ} (F : SkewedStabilityFunction C κ s a b)
    {X Y K : C} {ψ : ℝ}
    (hsum : F.charge X + F.charge Y = F.charge K)
    (hXle : F.phase X ≤ ψ) (hYlt : F.phase Y < ψ)
    (hYne : F.ChargeNe Y)
    (hXrange : F.phase X ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hYrange : F.phase Y ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hKrange : F.phase K ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    F.phase K < ψ := by
  have himX : rotatedIm (F.charge X) ψ ≤ 0 := by
    rw [rotatedIm_eq_norm_mul_sin (F.charge X) F.α ψ]
    apply mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _)
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by nlinarith [Real.pi_pos, hXle])
      (by nlinarith [Real.pi_pos, hXrange.1])
  have himY : rotatedIm (F.charge Y) ψ < 0 := by
    rw [rotatedIm_eq_norm_mul_sin (F.charge Y) F.α ψ]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hYne)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos, hYlt])
        (by nlinarith [Real.pi_pos, hYrange.1]))
  have himK : rotatedIm (F.charge K) ψ < 0 := by
    rw [← hsum]
    simpa [rotatedIm, add_mul, Complex.add_im] using
      (add_neg_of_nonpos_of_neg himX himY)
  exact relativePhase_lt_of_rotatedIm_neg himK hKrange

omit [IsTriangulated C] in
/-- The dual strict phase see-saw, packaged for an owner skewed stability
function. -/
theorem phase_seesaw_dual
    {s : Slicing C} {a b : ℝ} (F : SkewedStabilityFunction C κ s a b)
    {E E₁ E₂ : C} {ψ : ℝ}
    (hsum : F.charge E₁ + F.charge E₂ = F.charge E)
    (hψ : F.phase E = ψ)
    (hE₁gt : ψ < F.phase E₁)
    (hE₁ne : F.ChargeNe E₁)
    (hE₁range : F.phase E₁ ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hE₂range : F.phase E₂ ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    F.phase E₂ < ψ :=
  relativePhase_seesaw_dual hsum hψ hE₁gt hE₁ne hE₁range hE₂range

/-- Lowering the left endpoint of a thin interval preserves owner skewed
semistability. -/
theorem skewedSemistable_of_lower_inclusion
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a₁ a₂ b ψ ε : ℝ} (ha₁ : a₁ < b) (ha₂ : a₂ < b) (ha : a₂ ≤ a₁)
    (hε : 0 < ε) (hε4 : ε < 1 / 4)
    (haψ : a₁ + ε ≤ ψ) (hψb : ψ ≤ b - ε)
    (hthin₂ : b - a₂ + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C}
    (hSS : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW ha₁).IsSemistable
      E ψ) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW ha₂).IsSemistable
      E ψ := by
  have hEI₂ : σ.slicing.intervalProp C a₂ b E :=
    σ.slicing.intervalProp_mono C ha le_rfl E hSS.interval
  have ha₂ψ : a₂ + ε ≤ ψ := by linarith
  have hε2 : ε ≤ 1 / 2 := by linarith
  have hthin₁ : b - a₁ + 2 * ε < 1 := by linarith
  apply σ.skewedSemistable_of_target_triangleTest C W hr0 hr1 hW ha₁ ha₂
    hε hthin₂ ha₂ψ hψb hEI₂ hSS
  intro K Q i q δ hT hKI hQI hKne
  letI : Fact (a₂ < b) := ⟨ha₂⟩
  letI : Fact (b - a₂ ≤ 1) := ⟨by linarith⟩
  letI : Fact (a₁ < b) := ⟨ha₁⟩
  letI : Fact (b - a₁ ≤ 1) := ⟨by linarith⟩
  let KI₂ : σ.slicing.IntervalCat C a₂ b := ⟨K, hKI⟩
  let EI₂ : σ.slicing.IntervalCat C a₂ b := ⟨E, hEI₂⟩
  let QI₂ : σ.slicing.IntervalCat C a₂ b := ⟨Q, hQI⟩
  let iK : KI₂ ⟶ EI₂ := ObjectProperty.homMk i
  let qE : EI₂ ⟶ QI₂ := ObjectProperty.homMk q
  let S₀ : ShortComplex (σ.slicing.IntervalCat C a₂ b) :=
    ShortComplex.mk iK qE (by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hT)
  have hT₂ : Triangle.mk S₀.f.hom S₀.g.hom δ ∈ distTriang C := by
    simpa [S₀, iK, qE] using hT
  have hS₀ := Slicing.IntervalCat.strictShortExact_of_distinguished C σ.slicing hT₂
  have hiK : IsStrictMono iK := ⟨hS₀.shortExact.mono_f, hS₀.strict_f⟩
  obtain ⟨X, Y, fX, gY, δY, hTK, hX₁, hYle⟩ :=
    σ.slicing.exists_lower_boundary_triangle C ha₁ hKI
  have hX₂ : σ.slicing.intervalProp C a₂ b X :=
    σ.slicing.intervalProp_mono C ha le_rfl X hX₁
  have hY₂ : σ.slicing.intervalProp C a₂ b Y :=
    σ.slicing.intervalProp_of_lower_boundary_triangle C ha₁ ha hKI hX₁ hYle hTK
  let XI₁ : σ.slicing.IntervalCat C a₁ b := ⟨X, hX₁⟩
  let XI₂ : σ.slicing.IntervalCat C a₂ b := ⟨X, hX₂⟩
  let YI₂ : σ.slicing.IntervalCat C a₂ b := ⟨Y, hY₂⟩
  let EI₁ : σ.slicing.IntervalCat C a₁ b := ⟨E, hSS.interval⟩
  let xK : XI₂ ⟶ KI₂ := ObjectProperty.homMk fX
  let kY : KI₂ ⟶ YI₂ := ObjectProperty.homMk gY
  let S₁ : ShortComplex (σ.slicing.IntervalCat C a₂ b) :=
    ShortComplex.mk xK kY (by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hTK)
  have hTK₂ : Triangle.mk S₁.f.hom S₁.g.hom δY ∈ distTriang C := by
    simpa [S₁, xK, kY] using hTK
  have hS₁ := Slicing.IntervalCat.strictShortExact_of_distinguished C σ.slicing hTK₂
  have hxK : IsStrictMono xK := ⟨hS₁.shortExact.mono_f, hS₁.strict_f⟩
  let F₁ := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW ha₁
  let F₂ := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW ha₂
  by_cases hYZ : IsZero Y
  · have hK₁ : σ.slicing.intervalProp C a₁ b K :=
      σ.slicing.intervalProp_of_triangle C hX₁ (Or.inl hYZ) hTK
    have hKge : σ.slicing.geProp C (b - 1) K :=
      σ.slicing.geProp_anti C (by linarith) K
        (σ.slicing.geProp_of_gtProp C K (σ.slicing.gtProp_of_intervalProp C hK₁))
    have hQ₁ : σ.slicing.intervalProp C a₁ b Q :=
      σ.slicing.third_intervalProp_of_triangle C ha₁ hSS.interval hKge
        (σ.slicing.ltProp_of_intervalProp C hQI) hT
    have hphase₁ : F₁.phase K ≤ ψ :=
      hSS.phase_le_of_triangle hT hK₁ hQ₁ hKne
    have heq : F₁.phase K = F₂.phase K := by
      apply σ.skewedPhase_eq_of_common_interval C W hr0 hr1 hW ha₁ ha₂
        hε hε2 hthin₁ hsin
      · linarith
      · linarith
      · exact hK₁
      · exact hKne
    rwa [← heq]
  · by_cases hXZ : IsZero X
    · have hYlt : F₂.phase Y < ψ :=
        σ.skewedPhase_lt_of_leProp C W hr0 hr1 hW ha₂ hε hε2
          hthin₂ hsin ha₂ψ hψb hY₂ hYZ
          (σ.slicing.leProp_mono C (by linarith) Y hYle)
      haveI : IsIso gY :=
        (Triangle.isZero₁_iff_isIso₂ (Triangle.mk fX gY δY) hTK).mp hXZ
      have hKY : F₂.phase K = F₂.phase Y := F₂.phase_iso (asIso gY)
      rw [hKY]
      exact le_of_lt hYlt
    · let xE₂ : XI₂ ⟶ EI₂ := xK ≫ iK
      have hxE₂ : IsStrictMono xE₂ :=
        Slicing.IntervalCat.comp_strictMono C σ.slicing xK iK hxK hiK
      let xE₁ : XI₁ ⟶ EI₁ := ObjectProperty.homMk (fX ≫ i)
      have hmonoRH : Mono ((Slicing.IntervalCat.toRightHeart
          (C := C) (s := σ.slicing) a₁ b (Fact.out : b - a₁ ≤ 1)).map xE₁) := by
        let FR₁ := Slicing.IntervalCat.toRightHeart
          (C := C) (s := σ.slicing) a₁ b (Fact.out : b - a₁ ≤ 1)
        let FR₂ := Slicing.IntervalCat.toRightHeart
          (C := C) (s := σ.slicing) a₂ b (Fact.out : b - a₂ ≤ 1)
        let eX : FR₂.obj XI₂ ≅ FR₁.obj XI₁ := ObjectProperty.isoMk _ (Iso.refl X)
        let eE : FR₂.obj EI₂ ≅ FR₁.obj EI₁ := ObjectProperty.isoMk _ (Iso.refl E)
        letI : Mono (FR₂.map xE₂) :=
          Slicing.IntervalCat.mono_toRightHeart_of_strictMono C σ.slicing xE₂ hxE₂
        have heq : FR₁.map xE₁ = eX.inv ≫ FR₂.map xE₂ ≫ eE.hom := by
          apply ObjectProperty.hom_ext
          change fX ≫ i = 𝟙 X ≫ (fX ≫ i) ≫ 𝟙 E
          simp only [Category.id_comp, Category.comp_id]
        rw [heq]
        infer_instance
      have hxE₁ : IsStrictMono xE₁ := by
        letI : Mono ((Slicing.IntervalCat.toRightHeart
          (C := C) (s := σ.slicing) a₁ b (Fact.out : b - a₁ ≤ 1)).map xE₁) := hmonoRH
        exact Slicing.IntervalCat.strictMono_of_mono_toRightHeart C σ.slicing xE₁
      let SX : ShortComplex (σ.slicing.IntervalCat C a₁ b) :=
        ShortComplex.mk xE₁ (cokernel.π xE₁) (cokernel.condition xE₁)
      have hSX : StrictShortExact SX :=
        Slicing.IntervalCat.strictShortExact_cokernel C xE₁ hxE₁
      obtain ⟨δX, hTX⟩ :=
        Slicing.IntervalCat.exists_distinguished_of_strictShortExact C σ.slicing hSX
      have hXphase₁ : F₁.phase X ≤ ψ :=
        hSS.phase_le_of_triangle (by simpa [SX, xE₁] using hTX)
          hX₁ (cokernel xE₁).property hXZ
      have hXeq : F₁.phase X = F₂.phase X := by
        apply σ.skewedPhase_eq_of_common_interval C W hr0 hr1 hW ha₁ ha₂
          hε hε2 hthin₁ hsin
        · linarith
        · linarith
        · exact hX₁
        · exact hXZ
      have hXle : F₂.phase X ≤ ψ := hXeq ▸ hXphase₁
      have hYlt : F₂.phase Y < ψ :=
        σ.skewedPhase_lt_of_leProp C W hr0 hr1 hW ha₂ hε hε2
          hthin₂ hsin ha₂ψ hψb hY₂ hYZ
          (σ.slicing.leProp_mono C (by linarith) Y hYle)
      have hXrange := σ.skewedPhase_mem_enveloped_branch C W hr0 hr1 hW ha₂
        hε hε2 hthin₂ hsin ha₂ψ hψb hX₂ hXZ
      have hYrange := σ.skewedPhase_mem_enveloped_branch C W hr0 hr1 hW ha₂
        hε hε2 hthin₂ hsin ha₂ψ hψb hY₂ hYZ
      have hKrange := σ.skewedPhase_mem_enveloped_branch C W hr0 hr1 hW ha₂
        hε hε2 hthin₂ hsin ha₂ψ hψb hKI hKne
      exact le_of_lt (phase_add_lt_of_le_of_lt C F₂
        (F₂.charge_triangle (Triangle.mk fX gY δY) hTK).symm
        hXle hYlt
        (σ.charge_ne_of_interval C W hr0 hr1 hW ha₂ hε hε2 hthin₂ hsin hY₂ hYZ)
        hXrange hYrange hKrange)

/-- Raising the right endpoint of a thin interval preserves owner skewed
semistability. -/
theorem skewedSemistable_of_upper_inclusion
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b₁ b₂ ψ ε : ℝ} (hab₁ : a < b₁) (hab₂ : a < b₂) (hb : b₁ ≤ b₂)
    (hε : 0 < ε) (hε4 : ε < 1 / 4)
    (haψ : a + ε ≤ ψ) (hψb : ψ ≤ b₁ - ε)
    (hthin₂ : b₂ - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C}
    (hSS : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₁).IsSemistable
      E ψ) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₂).IsSemistable
      E ψ := by
  have hEI₂ : σ.slicing.intervalProp C a b₂ E :=
    σ.slicing.intervalProp_mono C le_rfl hb E hSS.interval
  have hψb₂ : ψ ≤ b₂ - ε := by linarith
  have hε2 : ε ≤ 1 / 2 := by linarith
  have hthin₁ : b₁ - a + 2 * ε < 1 := by linarith
  have hb₁a : b₁ ≤ a + 1 := by linarith
  apply σ.skewedSemistable_of_target_triangleTest C W hr0 hr1 hW hab₁ hab₂
    hε hthin₂ haψ hψb₂ hEI₂ hSS
  intro K Q i q δ hT hKI hQI hKne
  letI : Fact (a < b₂) := ⟨hab₂⟩
  letI : Fact (b₂ - a ≤ 1) := ⟨by linarith⟩
  let KI₂ : σ.slicing.IntervalCat C a b₂ := ⟨K, hKI⟩
  let EI₂ : σ.slicing.IntervalCat C a b₂ := ⟨E, hEI₂⟩
  let QI₂ : σ.slicing.IntervalCat C a b₂ := ⟨Q, hQI⟩
  let iK : KI₂ ⟶ EI₂ := ObjectProperty.homMk i
  let qE : EI₂ ⟶ QI₂ := ObjectProperty.homMk q
  let hcomp₀ : iK ≫ qE = 0 := by
    apply ObjectProperty.hom_ext
    change i ≫ q = 0
    exact comp_distTriang_mor_zero₁₂ _ hT
  let S₀ : ShortComplex (σ.slicing.IntervalCat C a b₂) :=
    ShortComplex.mk iK qE hcomp₀
  have hT₀ : Triangle.mk S₀.f.hom S₀.g.hom δ ∈ distTriang C := by
    simpa [S₀, iK, qE] using hT
  have hS₀ : StrictShortExact S₀ :=
    Slicing.IntervalCat.strictShortExact_of_distinguished C σ.slicing hT₀
  have hS₀Ker : IsLimit (KernelFork.ofι iK hcomp₀) := by
    simpa [S₀] using
      Slicing.IntervalCat.isLimitKernelForkOfDistinguished C hT₀
  obtain ⟨X, Y, fX, gY, δY, hTQ, hXge, hY₁⟩ :=
    σ.slicing.exists_upper_boundary_triangle C hab₁ hQI
  have hX₂ : σ.slicing.intervalProp C a b₂ X :=
    σ.slicing.intervalProp_of_upper_boundary_triangle C hab₁ hab₂ hb₁a
      hQI hXge hY₁ hTQ
  have hY₂ : σ.slicing.intervalProp C a b₂ Y :=
    σ.slicing.intervalProp_mono C le_rfl hb Y hY₁
  let XI₂ : σ.slicing.IntervalCat C a b₂ := ⟨X, hX₂⟩
  let YI₂ : σ.slicing.IntervalCat C a b₂ := ⟨Y, hY₂⟩
  let xQ : XI₂ ⟶ QI₂ := ObjectProperty.homMk fX
  let qY : QI₂ ⟶ YI₂ := ObjectProperty.homMk gY
  let hcomp₁ : xQ ≫ qY = 0 := by
    apply ObjectProperty.hom_ext
    change fX ≫ gY = 0
    exact comp_distTriang_mor_zero₁₂ _ hTQ
  let S₁ : ShortComplex (σ.slicing.IntervalCat C a b₂) :=
    ShortComplex.mk xQ qY hcomp₁
  have hT₁ : Triangle.mk S₁.f.hom S₁.g.hom δY ∈ distTriang C := by
    simpa [S₁, xQ, qY] using hTQ
  have hS₁ : StrictShortExact S₁ :=
    Slicing.IntervalCat.strictShortExact_of_distinguished C σ.slicing hT₁
  let F₁ := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₁
  let F₂ := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₂
  by_cases hXZ : IsZero X
  · have hQ₁ : σ.slicing.intervalProp C a b₁ Q :=
      σ.slicing.intervalProp_of_triangle C (Or.inl hXZ) hY₁ hTQ
    have hQle : σ.slicing.leProp C (a + 1) Q :=
      σ.slicing.leProp_mono C hb₁a Q
        (σ.slicing.leProp_of_ltProp C Q
          (σ.slicing.ltProp_of_intervalProp C hQ₁))
    have hKgt : σ.slicing.gtProp C a K :=
      σ.slicing.gtProp_of_intervalProp C hKI
    have hK₁ : σ.slicing.intervalProp C a b₁ K :=
      σ.slicing.first_intervalProp_of_triangle C hab₁ hSS.interval hQle hKgt hT
    have hphase₁ : F₁.phase K ≤ ψ :=
      hSS.phase_le_of_triangle hT hK₁ hQ₁ hKne
    have heq : F₁.phase K = F₂.phase K := by
      apply σ.skewedPhase_eq_of_common_interval C W hr0 hr1 hW hab₁ hab₂
        hε hε2 hthin₁ hsin
      · linarith
      · linarith
      · exact hK₁
      · exact hKne
    rw [← heq]
    exact hphase₁
  · have hqE : IsStrictEpi qE := ⟨hS₀.shortExact.epi_g, hS₀.strict_g⟩
    have hqY : IsStrictEpi qY := ⟨hS₁.shortExact.epi_g, hS₁.strict_g⟩
    haveI : Mono xQ := hS₁.shortExact.mono_f
    let BX : Subobject QI₂ := Subobject.mk xQ
    let PB : Subobject EI₂ := (Subobject.pullback qE).obj BX
    let hBXfac : BX.Factors (iK ≫ qE) := by
      rw [hcomp₀]
      exact (Subobject.factors_zero : BX.Factors (0 : KI₂ ⟶ QI₂))
    let hPBfac : PB.Factors iK := Limits.pullback_factors qE BX iK hBXfac
    let mPB : KI₂ ⟶ PB := PB.factorThru iK hPBfac
    let hcompL : mPB ≫ Subobject.pullbackπ qE BX = 0 := by
      apply (cancel_mono BX.arrow).1
      calc
        (mPB ≫ Subobject.pullbackπ qE BX) ≫ BX.arrow =
            mPB ≫ (Subobject.pullbackπ qE BX ≫ BX.arrow) := by simp
        _ = mPB ≫ (PB.arrow ≫ qE) := by
            rw [(Subobject.isPullback qE BX).w]
        _ = (mPB ≫ PB.arrow) ≫ qE := by simp
        _ = iK ≫ qE := by rw [Subobject.factorThru_arrow]
        _ = 0 := hcomp₀
        _ = 0 ≫ BX.arrow := by simp
    let SL : ShortComplex (σ.slicing.IntervalCat C a b₂) :=
      ShortComplex.mk mPB (Subobject.pullbackπ qE BX) hcompL
    have hLeft : StrictShortExact SL := by
      simpa [SL, PB, BX, mPB, hcompL] using
        Slicing.IntervalCat.strictShortExact_pullback_left C
          hcomp₀ hS₀Ker hqE BX
    have hBXcomp : BX.arrow ≫ qY = 0 := by
      calc
        BX.arrow ≫ qY = ((Subobject.underlyingIso xQ).hom ≫ xQ) ≫ qY := by
          rw [Subobject.underlyingIso_hom_comp_eq_mk xQ]
        _ = (Subobject.underlyingIso xQ).hom ≫ (xQ ≫ qY) := by simp
        _ = 0 := by simp [hcomp₁]
    have hS₁Ker : IsLimit (KernelFork.ofι xQ hcomp₁) := by
      simpa [S₁] using
        Slicing.IntervalCat.isLimitKernelForkOfDistinguished C hT₁
    have hBXKer : IsLimit (KernelFork.ofι BX.arrow hBXcomp) := by
      refine KernelFork.IsLimit.ofι' BX.arrow hBXcomp (fun {Z} k hk ↦ ?_)
      let uX : Z ⟶ XI₂ := hS₁Ker.lift (KernelFork.ofι k hk)
      refine ⟨uX ≫ (Subobject.underlyingIso xQ).inv, ?_⟩
      calc
        (uX ≫ (Subobject.underlyingIso xQ).inv) ≫ BX.arrow =
            uX ≫ xQ := by simp [Category.assoc, BX]
        _ = k := hS₁Ker.fac _ WalkingParallelPair.zero
    let pE : EI₂ ⟶ YI₂ := qE ≫ qY
    let hcompR : PB.arrow ≫ pE = 0 := by
      calc
        PB.arrow ≫ pE = PB.arrow ≫ qE ≫ qY := by simp [pE]
        _ = (PB.arrow ≫ qE) ≫ qY := by rw [Category.assoc]
        _ = (Subobject.pullbackπ qE BX ≫ BX.arrow) ≫ qY := by
            rw [(Subobject.isPullback qE BX).w]
        _ = 0 := by simp [hBXcomp]
    let SR : ShortComplex (σ.slicing.IntervalCat C a b₂) :=
      ShortComplex.mk PB.arrow pE hcompR
    have hRight : StrictShortExact SR := by
      simpa [SR, PB, BX, pE, hcompR] using
        Slicing.IntervalCat.strictShortExact_pullback_right C
          qE hqE BX qY hBXcomp hBXKer hqY
    haveI : Mono mPB := hLeft.shortExact.mono_f
    have hPBne : ¬IsZero (PB : σ.slicing.IntervalCat C a b₂).obj := by
      intro hPBzero
      have hPBzero' : IsZero (PB : σ.slicing.IntervalCat C a b₂) :=
        ObjectProperty.FullSubcategory.isZero_of_obj_isZero hPBzero
      have hKzero : IsZero KI₂ := IsZero.of_mono mPB hPBzero'
      exact hKne (((σ.slicing.intervalProp C a b₂).ι).map_isZero hKzero)
    obtain ⟨δR, hTR⟩ :=
      Slicing.IntervalCat.exists_distinguished_of_strictShortExact C σ.slicing hRight
    have hYle : σ.slicing.leProp C (a + 1) Y :=
      σ.slicing.leProp_mono C hb₁a Y
        (σ.slicing.leProp_of_ltProp C Y
          (σ.slicing.ltProp_of_intervalProp C hY₁))
    have hPBgt : σ.slicing.gtProp C a (PB : σ.slicing.IntervalCat C a b₂).obj :=
      σ.slicing.gtProp_of_intervalProp C
        (PB : σ.slicing.IntervalCat C a b₂).property
    have hPB₁ : σ.slicing.intervalProp C a b₁
        (PB : σ.slicing.IntervalCat C a b₂).obj :=
      σ.slicing.first_intervalProp_of_triangle C hab₁ hSS.interval hYle hPBgt
        (by simpa [SR, pE] using hTR)
    have hPBphase₁ : F₁.phase (PB : σ.slicing.IntervalCat C a b₂).obj ≤ ψ :=
      hSS.phase_le_of_triangle (by simpa [SR, pE] using hTR)
        hPB₁ hY₁ hPBne
    have hPBeq : F₁.phase (PB : σ.slicing.IntervalCat C a b₂).obj =
        F₂.phase (PB : σ.slicing.IntervalCat C a b₂).obj := by
      apply σ.skewedPhase_eq_of_common_interval C W hr0 hr1 hW hab₁ hab₂
        hε hε2 hthin₁ hsin
      · linarith
      · linarith
      · exact hPB₁
      · exact hPBne
    have hPBle : F₂.phase (PB : σ.slicing.IntervalCat C a b₂).obj ≤ ψ :=
      hPBeq ▸ hPBphase₁
    have hXgt : ψ < F₂.phase X :=
      σ.skewedPhase_gt_of_geProp C W hr0 hr1 hW hab₂ hε hε2
        hthin₂ hsin haψ hψb₂ hX₂ hXZ
        (σ.slicing.geProp_anti C (by linarith) X hXge)
    have hPBwindow := σ.skewedPhase_mem_expanded_interval C W hr0 hr1 hW hab₂
      hε hε2 hthin₂ hsin (PB : σ.slicing.IntervalCat C a b₂).property hPBne
    have hKwindow := σ.skewedPhase_mem_expanded_interval C W hr0 hr1 hW hab₂
      hε hε2 hthin₂ hsin hKI hKne
    have hXwindow := σ.skewedPhase_mem_expanded_interval C W hr0 hr1 hW hab₂
      hε hε2 hthin₂ hsin hX₂ hXZ
    let ψPB := F₂.phase (PB : σ.slicing.IntervalCat C a b₂).obj
    have hXrange : F₂.phase X ∈ Set.Ioo (ψPB - 1) (ψPB + 1) := by
      constructor <;> dsimp [ψPB] <;>
        linarith [hXwindow.1, hXwindow.2, hPBwindow.1, hPBwindow.2, hthin₂]
    have hKrange : F₂.phase K ∈ Set.Ioo (ψPB - 1) (ψPB + 1) := by
      constructor <;> dsimp [ψPB] <;>
        linarith [hKwindow.1, hKwindow.2, hPBwindow.1, hPBwindow.2, hthin₂]
    let eBX : (BX : σ.slicing.IntervalCat C a b₂).obj ≅ X :=
      ((σ.slicing.intervalProp C a b₂).ι).mapIso (Subobject.underlyingIso xQ)
    have hBXcharge : F₂.charge (BX : σ.slicing.IntervalCat C a b₂).obj =
        F₂.charge X :=
      congrArg F₂.W (classOf_iso C κ eBX)
    have hsumL' : F₂.charge (PB : σ.slicing.IntervalCat C a b₂).obj =
        F₂.charge K + F₂.charge (BX : σ.slicing.IntervalCat C a b₂).obj := by
      have hK₀ := Slicing.IntervalCat.K₀_of_strictShortExact C σ.slicing hLeft
      simpa only [SkewedStabilityFunction.charge, classOf, map_add] using
        congrArg (fun z : K₀ C ↦ F₂.W (κ z)) hK₀
    have hsumL : F₂.charge (PB : σ.slicing.IntervalCat C a b₂).obj =
        F₂.charge K + F₂.charge X := by
      rw [hsumL', hBXcharge]
    have hXgtPB : ψPB < F₂.phase X := by
      dsimp [ψPB]
      linarith
    have hKlt : F₂.phase K < ψPB := by
      exact phase_seesaw_dual C F₂
        (by simpa [add_comm] using hsumL.symm) rfl
        hXgtPB
        (σ.charge_ne_of_interval C W hr0 hr1 hW hab₂ hε hε2
          hthin₂ hsin hX₂ hXZ)
        hXrange hKrange
    dsimp [ψPB] at hKlt
    exact hKlt.le.trans hPBle

/-- Enlarging both endpoints of a thin interval preserves owner skewed
semistability. -/
theorem skewedSemistable_of_interval_inclusion
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a₁ a₂ b₁ b₂ ψ ε : ℝ}
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂)
    (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂)
    (hε : 0 < ε) (hε4 : ε < 1 / 4)
    (haψ : a₁ + ε ≤ ψ) (hψb : ψ ≤ b₁ - ε)
    (hthin₂ : b₂ - a₂ + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C}
    (hSS : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₁).IsSemistable
      E ψ) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₂).IsSemistable
      E ψ := by
  have habMid : a₁ < b₂ := by linarith
  have hthinMid : b₂ - a₁ + 2 * ε < 1 := by linarith
  have hmid := σ.skewedSemistable_of_upper_inclusion C W hr0 hr1 hW
    hab₁ habMid hb hε hε4 haψ hψb hthinMid hsin hSS
  exact σ.skewedSemistable_of_lower_inclusion C W hr0 hr1 hW
    habMid hab₂ ha hε hε4 (by linarith) (by linarith)
    hthin₂ hsin hmid

omit [IsTriangulated C] in
/-- Restricting a semistability presentation to a nested target interval
that still envelops its phase preserves owner skewed semistability. -/
theorem skewedSemistable_of_target_subinterval
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a₁ a₂ b₂ b₁ ψ ε : ℝ}
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂)
    (ha : a₁ ≤ a₂) (hb : b₂ ≤ b₁)
    {E : C}
    (hI₂ : σ.slicing.intervalProp C a₂ b₂ E)
    (hε : 0 < ε) (hε4 : ε < 1 / 4)
    (haψ : a₂ + ε ≤ ψ) (hψb : ψ ≤ b₂ - ε)
    (hthin₁ : b₁ - a₁ + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hSS : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₁).IsSemistable
      E ψ) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₂).IsSemistable
      E ψ := by
  have hε2 : ε ≤ 1 / 2 := by linarith
  exact σ.skewedSemistable_of_nested_interval C W hr0 hr1 hW
    hab₁ hab₂ hε hε2 hthin₁ hsin
    (by linarith) (by linarith) ha hb hI₂ hSS

/-- A semistability witness transports to every other thin old interval
containing the object and enveloping the same recorded phase. -/
theorem skewedSemistable_of_target_envelope
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a₁ a₂ b₁ b₂ ψ ε : ℝ}
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂)
    {E : C}
    (hI₂ : σ.slicing.intervalProp C a₂ b₂ E)
    (hε : 0 < ε) (hε4 : ε < 1 / 4)
    (ha₁ψ : a₁ + ε ≤ ψ) (hψb₁ : ψ ≤ b₁ - ε)
    (ha₂ψ : a₂ + ε ≤ ψ) (hψb₂ : ψ ≤ b₂ - ε)
    (hthin₁ : b₁ - a₁ + 2 * ε < 1)
    (hthin₂ : b₂ - a₂ + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hSS : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₁).IsSemistable
      E ψ) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₂).IsSemistable
      E ψ := by
  let a := max a₁ a₂
  let b := min b₁ b₂
  have ha₁ : a₁ ≤ a := le_max_left _ _
  have ha₂ : a₂ ≤ a := le_max_right _ _
  have hb₁ : b ≤ b₁ := min_le_left _ _
  have hb₂ : b ≤ b₂ := min_le_right _ _
  have hab : a < b := by
    dsimp [a, b]
    apply max_lt
    · exact lt_min hab₁ (by linarith)
    · exact lt_min (by linarith) hab₂
  have hI : σ.slicing.intervalProp C a b E := by
    by_cases hEZ : IsZero E
    · exact Or.inl hEZ
    · refine σ.slicing.intervalProp_of_intrinsic_phases C hEZ ?_ ?_
      · dsimp [a]
        exact max_lt_iff.mpr
          ⟨σ.slicing.phiMinus_gt_of_intervalProp C hEZ hSS.interval,
            σ.slicing.phiMinus_gt_of_intervalProp C hEZ hI₂⟩
      · dsimp [b]
        exact lt_min_iff.mpr
          ⟨σ.slicing.phiPlus_lt_of_intervalProp C hEZ hSS.interval,
            σ.slicing.phiPlus_lt_of_intervalProp C hEZ hI₂⟩
  have haψ : a + ε ≤ ψ := by
    dsimp [a]
    have hmax : max a₁ a₂ ≤ ψ - ε :=
      max_le (by linarith) (by linarith)
    linarith
  have hψb : ψ ≤ b - ε := by
    dsimp [b]
    rw [le_sub_iff_add_le]
    exact le_min (by linarith) (by linarith)
  have hthin : b - a + 2 * ε < 1 := by
    apply lt_of_le_of_lt (b := b₁ - a₁ + 2 * ε) _ hthin₁
    linarith
  have hmid := σ.skewedSemistable_of_target_subinterval C W hr0 hr1 hW
    hab₁ hab ha₁ hb₁ hI hε hε4 haψ hψb hthin₁ hsin hSS
  exact σ.skewedSemistable_of_interval_inclusion C W hr0 hr1 hW
    hab hab₂ ha₂ hb₂ hε hε4 haψ hψb hthin₂ hsin hmid

/-- Sharp owner Hom-vanishing for deformed slices, with target-envelope
transport discharged internally. -/
theorem hom_eq_zero_of_deformedPred
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E F : C} {ψ₁ ψ₂ : ℝ}
    (hE : σ.deformedPred C W hr0 hr1 hW ε ψ₁ E)
    (hF : σ.deformedPred C W hr0 hr1 hW ε ψ₂ F)
    (hgap : ψ₂ < ψ₁) (f : E ⟶ F) : f = 0 := by
  apply σ.hom_eq_zero_of_deformedPred_of_target_transport C W hr0 hr1 hW
    hε hε2 hε8 hsin
  · intro a b c d ψ X hab hcd hthin₁ hthin₂ haψ hψb hcψ hψd hI hSS
    exact σ.skewedSemistable_of_target_envelope C W hr0 hr1 hW
      hab hcd hI hε (by linarith) haψ hψb hcψ hψd
      hthin₁ hthin₂ hsin hSS
  · exact hE
  · exact hF
  · exact hgap

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
