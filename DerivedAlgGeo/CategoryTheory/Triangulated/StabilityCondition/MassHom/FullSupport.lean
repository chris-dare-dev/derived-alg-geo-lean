/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Distance.Separation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Support.Semistable

/-!
# Full support from mass--Hom bounds

This file formalizes the categorical core of Cheng's full-support argument
(arXiv:2608.14540v1, Theorem 2.1).  A finite family of test objects supplies
Euler probes on the real numerical class space.  If those probes separate
classes and a finite Ext-window controls every probe on semistable objects,
then a mass--Hom bound produces one genuine Kontsevich--Soibelman quadratic
support form.

The Ext-window is deliberately an explicit hypothesis.  Its geometric proof
uses phase vanishing and Grothendieck--Serre duality with a dualizing complex;
none of that geometry is manufactured in this categorical layer.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.Support
open CategoryTheory.SerreFunctor
open scoped BigOperators ENNReal

namespace CategoryTheory.Triangulated.StabilityCondition.WithClassMap

noncomputable section

universe w v u u'

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]
  [Pretriangulated C] [IsTriangulated C]
  [HomFinite k C] [HomFiniteBounded k C]
variable {V : Type u'} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {v₀ : K₀ C →+ V}
variable {ι : Type*} [Fintype ι]

/-- A finite collection of test objects whose Euler pairings extend to
real-linear functionals separating the full real numerical class space.

The `realizes` field is the precise bridge to the Hom-built Euler form.  The
extension and separation are input: this file does not infer either from a
presentation of the numerical Grothendieck group. -/
structure EulerProbeFamily (A : ι → C) (probe : ι → V →ₗ[ℝ] ℝ) : Prop where
  /-- The real probe extends `χ(Aᵢ,-)` along the chosen class map. -/
  realizes : ∀ (i : ι) (x : K₀ C),
    probe i (v₀ x) = (chiK₀ k C (K₀.of C (A i)) x : ℝ)
  /-- The finite family of extended Euler probes separates all real classes. -/
  separates : ∀ x : V, (∀ i : ι, probe i x = 0) → x = 0

/-- The finite Ext-window needed in Cheng's argument.

For each Euler test `A i`, `shifts i` lists the only shifted tests needed to
bound its Euler pairing on a semistable object.  The shifted tests are required
to lie in the mass--Hom test class `T`.  The final field is exactly the
triangle-inequality estimate furnished geometrically by phase vanishing and
Serre duality; it remains explicit until those geometric bridges exist. -/
structure SemistableExtWindow
    (s : StabilityCondition.WithClassMap C v₀) (T : ObjectProperty C)
    (A : ι → C) where
  /-- The finite set of relevant Ext-degrees for each Euler test. -/
  shifts : ι → Finset ℤ
  /-- Every shifted source occurring in the window belongs to the test class. -/
  shifted_mem : ∀ (i : ι) (j : ℤ), j ∈ shifts i → T ((A i)⟦-j⟧)
  /-- On semistables, the absolute Euler pairing is bounded by the Hom-dimensions
  in the declared finite window. -/
  euler_abs_le : ∀ (i : ι) (P : ℝ) (F : C), s.slicing.P P F →
    |(chiHom k C (A i) F : ℝ)| ≤
      ∑ j ∈ shifts i, (Module.finrank k ((A i)⟦-j⟧ ⟶ F) : ℝ)

namespace FullSupport

/-- The sum-of-squares quadratic form attached to a finite family of real
linear probes. -/
def probeQuadratic (probe : ι → V →ₗ[ℝ] ℝ) : QuadraticForm ℝ V :=
  ∑ i, QuadraticMap.linMulLin (probe i) (probe i)

omit [FiniteDimensional ℝ V] in
@[simp]
theorem probeQuadratic_apply (probe : ι → V →ₗ[ℝ] ℝ) (x : V) :
    probeQuadratic probe x = ∑ i, (probe i x) ^ 2 := by
  simp [probeQuadratic, pow_two]

/-- The quadratic form `x ↦ ‖Zx‖²`, written algebraically using the real
and imaginary coordinate functionals of the complex charge. -/
def chargeQuadratic (Z : V →ₗ[ℝ] ℂ) : QuadraticForm ℝ V :=
  QuadraticMap.linMulLin (Complex.reLm.comp Z) (Complex.reLm.comp Z) +
    QuadraticMap.linMulLin (Complex.imLm.comp Z) (Complex.imLm.comp Z)

omit [FiniteDimensional ℝ V] in
@[simp]
theorem chargeQuadratic_apply (Z : V →ₗ[ℝ] ℂ) (x : V) :
    chargeQuadratic Z x = ‖Z x‖ ^ 2 := by
  rw [chargeQuadratic, QuadraticMap.add_apply,
    QuadraticMap.linMulLin_apply, QuadraticMap.linMulLin_apply]
  simpa [Complex.normSq_apply] using Complex.normSq_eq_norm_sq (Z x)

omit [FiniteDimensional ℝ V] in
/-- Finite separating probes with uniform linear charge bounds produce a
genuine quadratic support form. -/
theorem hasQuadraticSupportProperty_of_finite_probes
    (Z : V →ₗ[ℝ] ℂ) (S : Set V) (probe : ι → V →ₗ[ℝ] ℝ)
    (hsep : ∀ x : V, (∀ i : ι, probe i x = 0) → x = 0)
    (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hbound : ∀ x ∈ S, ∀ i, |probe i x| ≤ B i * ‖Z x‖) :
    HasQuadraticSupportProperty Z S := by
  let D : ℝ := ∑ i, (B i) ^ 2
  let Q : QuadraticForm ℝ V :=
    D • chargeQuadratic Z - probeQuadratic probe
  refine ⟨Q, ?_⟩
  constructor
  · intro x hx
    have hsq : ∀ i, (probe i x) ^ 2 ≤ (B i * ‖Z x‖) ^ 2 := by
      intro i
      rw [sq_le_sq]
      simpa [abs_mul, abs_of_nonneg (hB i), abs_of_nonneg (norm_nonneg _)] using
        hbound x hx i
    have hsum : ∑ i, (probe i x) ^ 2 ≤ D * ‖Z x‖ ^ 2 := by
      calc
        ∑ i, (probe i x) ^ 2 ≤ ∑ i, (B i * ‖Z x‖) ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ hsq i
        _ = D * ‖Z x‖ ^ 2 := by
          simp only [mul_pow, D, Finset.sum_mul]
    simp only [Q, QuadraticMap.sub_apply, QuadraticMap.smul_apply,
      chargeQuadratic_apply, probeQuadratic_apply, smul_eq_mul]
    linarith
  · intro x hxZ hx
    have hprobe : 0 < probeQuadratic probe x := by
      rw [probeQuadratic_apply]
      have hex : ∃ i : ι, probe i x ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hx (hsep x hall)
      obtain ⟨i, hi⟩ := hex
      exact Finset.sum_pos' (fun j _ ↦ sq_nonneg (probe j x))
        ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    simp [Q, hxZ]
    simpa only [probeQuadratic_apply] using hprobe

end FullSupport

omit [FiniteDimensional ℝ V] in
/-- Cheng's categorical full-support argument: a mass--Hom bound, finitely many
separating Euler probes, and an explicit semistable Ext-window imply genuine
quadratic support on the full real numerical class space. -/
theorem HasMassHomBound.quadraticSupportData
    (s : StabilityCondition.WithClassMap C v₀) (T : ObjectProperty C)
    (hs : s.HasMassHomBound (k := k) T)
    (A : ι → C) (probe : ι → V →ₗ[ℝ] ℝ)
    (hprobe : EulerProbeFamily (k := k) (v₀ := v₀) A probe)
    (hwindow : SemistableExtWindow (k := k) s T A)
    (Zlin : V →ₗ[ℝ] ℂ) (hZ : ∀ x : V, Zlin x = s.Z x) :
    s.toWithClassMap.QuadraticSupportData Zlin := by
  let K : ι → ℤ → ℝ := fun i j ↦
    if hj : j ∈ hwindow.shifts i then
      Classical.choose (hs ((A i)⟦-j⟧) (hwindow.shifted_mem i j hj))
    else 0
  let B : ι → ℝ := fun i ↦ ∑ j ∈ hwindow.shifts i, K i j
  have hK_nonneg : ∀ i j, 0 ≤ K i j := by
    intro i j
    by_cases hj : j ∈ hwindow.shifts i
    · simp only [K, dif_pos hj]
      exact (Classical.choose_spec
        (hs ((A i)⟦-j⟧) (hwindow.shifted_mem i j hj))).1.le
    · simp [K, hj]
  have hB : ∀ i, 0 ≤ B i := fun i ↦
    Finset.sum_nonneg fun j _ ↦ hK_nonneg i j
  refine ⟨hZ, FullSupport.hasQuadraticSupportProperty_of_finite_probes
    Zlin s.toWithClassMap.semistableClasses probe hprobe.separates B hB ?_⟩
  intro x hx i
  obtain ⟨P, F, hPF, hF, rfl⟩ := hx
  rw [hprobe.realizes, chiK₀_of_of]
  calc
    |(chiHom k C (A i) F : ℝ)| ≤
        ∑ j ∈ hwindow.shifts i,
          (Module.finrank k ((A i)⟦-j⟧ ⟶ F) : ℝ) :=
      hwindow.euler_abs_le i P F hPF
    _ ≤ ∑ j ∈ hwindow.shifts i,
        K i j * (stabilityMass s F).toReal := by
      refine Finset.sum_le_sum fun j hj ↦ ?_
      simp only [K, dif_pos hj]
      exact (Classical.choose_spec
        (hs ((A i)⟦-j⟧) (hwindow.shifted_mem i j hj))).2 F
    _ = B i * ‖Zlin (v₀ (K₀.of C F))‖ := by
      rw [← Finset.sum_mul]
      change B i * (stabilityMass s F).toReal =
        B i * ‖Zlin (v₀ (K₀.of C F))‖
      rw [hZ, ← stabilityMass_toReal_eq_norm_charge s hPF]

end

end CategoryTheory.Triangulated.StabilityCondition.WithClassMap
