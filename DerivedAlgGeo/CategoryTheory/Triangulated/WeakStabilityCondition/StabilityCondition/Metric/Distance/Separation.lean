/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Metric.Distance.Basic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Separation for the full stability distance

The three-coordinate distance determines the slicing and every charge visible
through the class map.  More precisely, distance zero implies equality of the
two slicings and of the composites `Z.comp v : K₀ C →+ ℂ`.

For `StabilityCondition.WithClassMap C v`, literal equality of the stored
central charges on `Λ` additionally requires `v` to be surjective.  Some
hypothesis is genuinely needed — the distance only ever evaluates the charge on
classes in the image of `v`, so nothing constrains the two charges off that
image.  Surjectivity is **sufficient, not necessary**: since `ℂ` is
torsion-free, `Λ / range v` being torsion already suffices.  Surjectivity is
used because it is the hypothesis the `(Λ, v)` literature carries by
definition.  In the ordinary specialization `StabilityCondition C`, the class
map is the identity and separation is unconditional.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Complex
open scoped ENNReal ZeroObject

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

omit [IsTriangulated C] in
/-- Every objectwise term vanishes when the full distance vanishes. -/
theorem stabilityDistTerm_eq_zero_of_eq_zero
    {σ τ : StabilityCondition.WithClassMap C v}
    (hd : stabilityDist σ τ = 0) (E : C) (hE : ¬IsZero E) :
    stabilityDistTerm σ τ E hE = 0 := by
  have hle : stabilityDistTerm σ τ E hE ≤ stabilityDist σ τ := by
    unfold stabilityDist
    exact le_iSup₂ (f := fun (X : C) (hX : ¬IsZero X) ↦
      stabilityDistTerm σ τ X hX) E hE
  rw [hd] at hle
  exact le_antisymm hle zero_le

omit [IsTriangulated C] in
/-- Distance zero identifies the intrinsic highest phase of every nonzero
object. -/
theorem phiPlus_eq_of_stabilityDist_eq_zero
    {σ τ : StabilityCondition.WithClassMap C v}
    (hd : stabilityDist σ τ = 0) (E : C) (hE : ¬IsZero E) :
    σ.slicing.phiPlus C E hE = τ.slicing.phiPlus C E hE := by
  have hterm := stabilityDistTerm_eq_zero_of_eq_zero hd E hE
  have hcoord : phiPlusDist σ τ E hE = 0 := by
    apply bot_unique
    exact (le_max_left _ _).trans_eq hterm
  simpa only [phiPlusDist, ENNReal.ofReal_eq_zero, abs_nonpos_iff,
    sub_eq_zero] using hcoord

omit [IsTriangulated C] in
/-- Distance zero identifies the intrinsic lowest phase of every nonzero
object. -/
theorem phiMinus_eq_of_stabilityDist_eq_zero
    {σ τ : StabilityCondition.WithClassMap C v}
    (hd : stabilityDist σ τ = 0) (E : C) (hE : ¬IsZero E) :
    σ.slicing.phiMinus C E hE = τ.slicing.phiMinus C E hE := by
  have hterm := stabilityDistTerm_eq_zero_of_eq_zero hd E hE
  have hcoord : phiMinusDist σ τ E hE = 0 := by
    apply bot_unique
    exact (le_trans (le_max_left _ _) (le_max_right _ _)).trans_eq hterm
  simpa only [phiMinusDist, ENNReal.ofReal_eq_zero, abs_nonpos_iff,
    sub_eq_zero] using hcoord

/-- The mass coordinate of a nonzero object agrees at distance zero. -/
theorem stabilityMass_toReal_eq_of_stabilityDist_eq_zero
    {σ τ : StabilityCondition.WithClassMap C v}
    (hd : stabilityDist σ τ = 0) (E : C) (hE : ¬IsZero E) :
    (stabilityMass σ E).toReal = (stabilityMass τ E).toReal := by
  have hterm := stabilityDistTerm_eq_zero_of_eq_zero hd E hE
  have hcoord : massDist σ τ E = 0 := by
    apply bot_unique
    exact (le_trans (le_max_right _ _) (le_max_right _ _)).trans_eq hterm
  rw [massDist_eq_abs_log] at hcoord
  have hlog : Real.log (stabilityMass σ E).toReal =
      Real.log (stabilityMass τ E).toReal := by
    simpa only [ENNReal.ofReal_eq_zero, abs_nonpos_iff, sub_eq_zero] using hcoord
  exact Real.log_injOn_pos
    (stabilityMass_toReal_pos σ hE) (stabilityMass_toReal_pos τ hE) hlog

/-- A semistable object's real mass is the norm of its charge. -/
theorem stabilityMass_toReal_eq_norm_charge
    (σ : StabilityCondition.WithClassMap C v) {E : C} {φ : ℝ}
    (hP : σ.slicing.P φ E) :
    (stabilityMass σ E).toReal = ‖σ.charge E‖ := by
  rw [stabilityMass_eq_ofReal_norm_charge σ hP]
  exact ENNReal.toReal_ofReal (norm_nonneg _)

omit [IsTriangulated C] in
/-- Distance zero identifies the two slicings. -/
theorem slicing_eq_of_stabilityDist_eq_zero
    {σ τ : StabilityCondition.WithClassMap C v}
    (hd : stabilityDist σ τ = 0) : σ.slicing = τ.slicing := by
  apply Slicing.ext C
  funext φ E
  apply propext
  constructor
  · intro hσ
    by_cases hE : IsZero E
    · exact τ.slicing.zero_mem_of_isZero C φ E hE
    have hp := phiPlus_eq_of_stabilityDist_eq_zero hd E hE
    have hm := phiMinus_eq_of_stabilityDist_eq_zero hd E hE
    have hσphase := σ.slicing.phiPlus_eq_phiMinus_of_semistable C hσ hE
    have hτeq : τ.slicing.phiPlus C E hE = τ.slicing.phiMinus C E hE := by
      rw [← hp, ← hm, hσphase.1, hσphase.2]
    have hτ := τ.slicing.semistable_of_phiPlus_eq_phiMinus C hE hτeq
    simpa only [← hp, hσphase.1] using hτ
  · intro hτ
    by_cases hE : IsZero E
    · exact σ.slicing.zero_mem_of_isZero C φ E hE
    have hp := phiPlus_eq_of_stabilityDist_eq_zero hd E hE
    have hm := phiMinus_eq_of_stabilityDist_eq_zero hd E hE
    have hτphase := τ.slicing.phiPlus_eq_phiMinus_of_semistable C hτ hE
    have hσeq : σ.slicing.phiPlus C E hE = σ.slicing.phiMinus C E hE := by
      rw [hp, hm, hτphase.1, hτphase.2]
    have hσ := σ.slicing.semistable_of_phiPlus_eq_phiMinus C hE hσeq
    simpa only [hp, hτphase.1] using hσ

/-- Distance zero identifies the charge of every object.  This statement does
not require surjectivity of the class map. -/
theorem charge_eq_of_stabilityDist_eq_zero
    {σ τ : StabilityCondition.WithClassMap C v}
    (hd : stabilityDist σ τ = 0) (E : C) : σ.charge E = τ.charge E := by
  have hslicing := slicing_eq_of_stabilityDist_eq_zero hd
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.charge_postnikovTower_eq_sum F.toPostnikovTower,
    τ.charge_postnikovTower_eq_sum F.toPostnikovTower]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : IsZero (F.factor i)
  · rw [σ.charge_isZero hi, τ.charge_isZero hi]
  have hPσ : σ.slicing.P (F.φ i) (F.factor i) := F.semistable i
  have hPτ : τ.slicing.P (F.φ i) (F.factor i) := by
    rw [← hslicing]
    exact hPσ
  obtain ⟨mσ, hmσ, hσ⟩ := σ.compat (F.φ i) (F.factor i) hPσ hi
  obtain ⟨mτ, hmτ, hτ⟩ := τ.compat (F.φ i) (F.factor i) hPτ hi
  have hmass := stabilityMass_toReal_eq_of_stabilityDist_eq_zero
    hd (F.factor i) hi
  have hnorm : ‖σ.charge (F.factor i)‖ = ‖τ.charge (F.factor i)‖ := by
    rw [← stabilityMass_toReal_eq_norm_charge σ hPσ,
      ← stabilityMass_toReal_eq_norm_charge τ hPτ]
    exact hmass
  have hmσnorm : ‖σ.charge (F.factor i)‖ = mσ := by
    rw [hσ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmσ,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hmτnorm : ‖τ.charge (F.factor i)‖ = mτ := by
    rw [hτ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmτ,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hm : mσ = mτ := hmσnorm.symm.trans (hnorm.trans hmτnorm)
  rw [hσ, hτ, hm]

/-- Unconditionally, distance zero identifies the observable central charge
`Z ∘ v` on `K₀ C`. -/
theorem charge_comp_eq_of_stabilityDist_eq_zero
    {σ τ : StabilityCondition.WithClassMap C v}
    (hd : stabilityDist σ τ = 0) : σ.Z.comp v = τ.Z.comp v := by
  apply K₀.hom_ext (C := C)
  intro E
  exact charge_eq_of_stabilityDist_eq_zero hd E

/-- For a surjective class map, the full stability distance separates points. -/
theorem stabilityDist_eq_zero
    {σ τ : StabilityCondition.WithClassMap C v}
    (hv : Function.Surjective v) (hd : stabilityDist σ τ = 0) : σ = τ := by
  apply StabilityCondition.WithClassMap.ext (C := C)
  · exact slicing_eq_of_stabilityDist_eq_zero hd
  · have hcomp := charge_comp_eq_of_stabilityDist_eq_zero hd
    ext x
    obtain ⟨y, rfl⟩ := hv x
    exact DFunLike.congr_fun hcomp y

/-- Identity of indiscernibles for a surjective class map.

Deliberately NOT `@[simp]`: `Function.Surjective v` is not equation-theorem
shaped, so simp's default discharger never consults the context, and
`Function.surjective_id` is not itself `@[simp]` -- the rewrite would be inert
even at `v = id`. The unconditional `stabilityConditionDist_eq_zero_iff` below
carries the attribute instead. -/
theorem stabilityDist_eq_zero_iff
    {σ τ : StabilityCondition.WithClassMap C v}
    (hv : Function.Surjective v) : stabilityDist σ τ = 0 ↔ σ = τ := by
  constructor
  · exact stabilityDist_eq_zero hv
  · rintro rfl
    exact stabilityDist_self σ

/-- The ordinary stability distance on charges over `K₀ C` separates points
without an additional hypothesis. -/
theorem stabilityConditionDist_eq_zero
    {σ τ : StabilityCondition C} (hd : stabilityDist σ τ = 0) : σ = τ :=
  stabilityDist_eq_zero (Function.surjective_id) hd

/-- Identity of indiscernibles for ordinary stability conditions. -/
@[simp, cites "stmt:a520a8d4f877:bridgeland2007.prop-8.1" (relation := no_claim)
        (note := "The identity-of-indiscernibles clause for the literal finite HN-mass distance on ordinary stability conditions. The comparison between the distance-induced topology and the Section 6 topology remains unproved, so the complete proposition is not claimed.")]
theorem stabilityConditionDist_eq_zero_iff
    {σ τ : StabilityCondition C} : stabilityDist σ τ = 0 ↔ σ = τ := by
  constructor
  · exact stabilityConditionDist_eq_zero
  · rintro rfl
    exact stabilityDist_self σ

end

end CategoryTheory.Triangulated
