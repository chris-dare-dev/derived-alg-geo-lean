/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.Theorem
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Support.LocallyFinite
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.ChargeNormalization

/-!
# Deforming a stability condition with the support property

Let `σ` be a stability condition whose classes land, with discrete image, in a
finite-dimensional real space `V`, and let `Zlin : V →ₗ[ℝ] ℂ` realize its central
charge. This file feeds the support property into the repository's deformation
theorem `StabilityCondition.WithClassMap.deformed`, which is Bridgeland's
Theorem 7.1. It is the second step of the proof of Theorem 12.11 of
arXiv:1902.08184v4 (BLMNPS) along Bayer, arXiv:1606.02169.

Two inputs of `deformed` come from the support property.

* **The radius.** `deformed` asks for a radius `ε₀ < 1/16` such that every thin
  interval of radius `4 ε₀` has finite length (`WideSectorFiniteLength`). Local
  finiteness alone gives some radius depending on `σ`. The support property gives
  every `ε₀ ≤ 1/16` at once, because the proof of Remark 12.3 of BLMNPS bounds
  strict chains in every interval of radius `1/4`
  (`isStrictFiniteLength_of_hasSupportProperty`). This is the uniform step size
  that path lifting in Theorem 12.11 needs.
* **The seminorm.** If `W` stays within `c ‖Z x‖` of `Z x` on the classes of
  semistable objects, then `‖W - Z‖_σ ≤ c`. For a normalized pair `(Q, Zlin)`
  (`QuadraticMap.IsNormalized`, Bayer's equation (2)) and
  `W = Zlin + u ∘ kerProj Q Zlin`, Bayer's estimate
  `QuadraticMap.IsNormalized.normalized_charge_bound` holds on the cone `0 ≤ Q`,
  which contains every semistable class.

## Main definitions

* `StabilityCondition.WithClassMap.deformedOfSupport`: the deformation of `σ`
  with charge `W`, for `‖W - Z‖_σ ≤ c < sin (π ε)` and `ε < 1/32`, with the radius
  supplied by the support property.

## Main results

* `wideSectorFiniteLength_of_hasSupportProperty`: every `ε₀ ≤ 1/16` is a
  deformation radius.
* `stabilitySeminorm_le_of_forall_semistableClasses`: a bound on semistable
  classes bounds the stability seminorm.
* `stabilitySeminorm_le_of_normalized`: `‖(Zlin + u ∘ kerProj Q Zlin) - Z‖_σ ≤ c`
  when `u` has norm at most `c` for `√(-Q)`.
* `slicingDist_deformedOfSupport_le`: the deformation moves the slicing by at most
  `ε`.
* `exists_deformed_of_normalized`: for `‖u‖ ≤ c < sin (π ε)`, some stability
  condition has charge `Zlin + u ∘ kerProj Q Zlin` and slicing within `ε` of `σ`.

## Implementation notes

The bound `ε < 1/32` comes from the hypotheses `ε < ε₀ / 2` and `ε₀ < 1/16` of
`deformed`; `deformedOfSupport` takes `ε₀ = ε + 1/32`. The norm of `u` is
expressed, as in `ChargeNormalization`, through `‖u k‖ ^ 2 ≤ c ^ 2 * -Q k`.

## References

* Bayer, Lahoz, Macrì, Nuer, Perry, Stellari, arXiv:1902.08184v4, Remark 12.3 and
  Theorem 12.11.
* Bayer, *A short proof of the deformation property of Bridgeland stability
  conditions*, arXiv:1606.02169, equation (2) and the proof of Lemma 5.7.
* Bridgeland, *Stability conditions on triangulated categories* (2007),
  Theorem 7.1.

## Tags

stability condition, support property, deformation, quadratic form
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation
open CategoryTheory.Triangulated.WeakStabilityCondition.Support
open scoped ENNReal

namespace CategoryTheory.Triangulated.StabilityCondition.WithClassMap

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {κ : K₀ C →+ V}

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A bound on `W - Z` relative to `Z` over the classes of nonzero semistable
objects bounds the stability seminorm of `W - Z`. -/
theorem stabilitySeminorm_le_of_forall_semistableClasses
    (σ : StabilityCondition.WithClassMap C κ) (W : V →+ ℂ) {c : ℝ}
    (hW : ∀ x ∈ σ.semistableClasses, ‖W x - σ.Z x‖ ≤ c * ‖σ.Z x‖) :
    stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal c := by
  refine iSup_le fun E => iSup_le fun φ => iSup_le fun hP => iSup_le fun hE => ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (charge_norm_pos C σ hP hE), AddMonoidHom.sub_apply]
  exact hW _ (σ.class_mem_semistableClasses hP hE)

/-- **The seminorm bound for a normalized pair** (Bayer, proof of Lemma 5.7).

Let `Q` be nonnegative on the classes of semistable objects of `σ`, and let the
pair `(Q, Zlin)` be normalized. If `u : ker Zlin → ℂ` has norm at most `c` for the
norm `√(-Q)` on `ker Zlin`, then the charge `W = Zlin + u ∘ kerProj Q Zlin`
satisfies `‖W - Z‖_σ ≤ c`. -/
theorem stabilitySeminorm_le_of_normalized
    (σ : StabilityCondition.WithClassMap C κ) {Zlin : V →ₗ[ℝ] ℂ}
    (hZ : ∀ x, Zlin x = σ.Z x) {Q : QuadraticForm ℝ V}
    (hQ : IsCompatible Zlin σ.semistableClasses Q) (hN : QuadraticMap.IsNormalized Q Zlin)
    {u : LinearMap.ker Zlin →ₗ[ℝ] ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hu : ∀ k, ‖u k‖ ^ 2 ≤ c ^ 2 * -Q k) :
    stabilitySeminorm C σ
        ((Zlin + u ∘ₗ QuadraticMap.kerProj Q Zlin).toAddMonoidHom - σ.Z) ≤
      ENNReal.ofReal c :=
  stabilitySeminorm_le_of_forall_semistableClasses σ _ fun x hx => by
    rw [← hZ]
    exact hN.normalized_charge_bound hc hu (hQ.nonneg_of_mem x hx)

variable [IsTriangulated C]

/-- **The deformation radius from the support property.**

If the classes of `σ` have discrete image and satisfy the support property, then
every `ε₀ ≤ 1/16` is a radius for `deformed`: every thin interval of radius
`4 ε₀` has finite length. The radius does not depend on `σ`. -/
theorem wideSectorFiniteLength_of_hasSupportProperty
    (σ : StabilityCondition.WithClassMap C κ) (hκ : DiscreteTopology (Set.range κ))
    {Zlin : V →ₗ[ℝ] ℂ} (hZ : ∀ x, Zlin x = σ.Z x) (hS : σ.HasSupportProperty Zlin)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀16 : ε₀ ≤ 1 / 16) :
    WideSectorFiniteLength C σ ε₀ := by
  intro t E
  have : Fact (t - 4 * ε₀ < t + 4 * ε₀) := ⟨by linarith⟩
  have : Fact ((t + 4 * ε₀) - (t - 4 * ε₀) ≤ 1) := ⟨by linarith⟩
  have : Fact (t - 1 / 4 < t + 1 / 4) := ⟨by linarith⟩
  have : Fact ((t + 1 / 4) - (t - 1 / 4) ≤ 1) := ⟨by linarith⟩
  exact Slicing.IntervalCat.isFiniteLength_of_isStrictFiniteLength C σ.slicing
    (interval_strictFiniteLength_of_inclusion C
      (σ.slicing.intervalProp_mono C (by linarith) (by linarith))
      (fun Y => σ.isStrictFiniteLength_of_hasSupportProperty κ hκ Zlin
        (fun x => hZ (κ x)) hS t Y) E)

/-- **Deformation of a stability condition with the support property.**

If `‖W - Z‖_σ ≤ c < sin (π ε)` with `0 < ε < 1/32`, this is the stability
condition `deformed` produces with central charge `W`. The radius `ε + 1/32` is
supplied by `wideSectorFiniteLength_of_hasSupportProperty`. -/
def deformedOfSupport
    (σ : StabilityCondition.WithClassMap C κ) (hκ : DiscreteTopology (Set.range κ))
    {Zlin : V →ₗ[ℝ] ℂ} (hZ : ∀ x, Zlin x = σ.Z x) (hS : σ.HasSupportProperty Zlin)
    (W : V →+ ℂ) {c ε : ℝ} (hc : 0 ≤ c)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal c)
    (hε : 0 < ε) (hε32 : ε < 1 / 32) (hcε : c < Real.sin (Real.pi * ε)) :
    StabilityCondition.WithClassMap C κ :=
  σ.deformed C W hc (hcε.trans_le (Real.sin_le_one _)) hW (ε₀ := ε + 1 / 32)
    (by linarith) (by linarith)
    (σ.wideSectorFiniteLength_of_hasSupportProperty hκ hZ hS (by linarith) (by linarith))
    hε (by linarith) (by linarith) (by linarith)
    (hW.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hc.trans_lt hcε)).mpr hcε))

@[simp]
theorem deformedOfSupport_Z
    (σ : StabilityCondition.WithClassMap C κ) (hκ : DiscreteTopology (Set.range κ))
    {Zlin : V →ₗ[ℝ] ℂ} (hZ : ∀ x, Zlin x = σ.Z x) (hS : σ.HasSupportProperty Zlin)
    (W : V →+ ℂ) {c ε : ℝ} (hc : 0 ≤ c)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal c)
    (hε : 0 < ε) (hε32 : ε < 1 / 32) (hcε : c < Real.sin (Real.pi * ε)) :
    (σ.deformedOfSupport hκ hZ hS W hc hW hε hε32 hcε).Z = W :=
  rfl

/-- The deformation moves the slicing by at most `ε`. -/
theorem slicingDist_deformedOfSupport_le
    (σ : StabilityCondition.WithClassMap C κ) (hκ : DiscreteTopology (Set.range κ))
    {Zlin : V →ₗ[ℝ] ℂ} (hZ : ∀ x, Zlin x = σ.Z x) (hS : σ.HasSupportProperty Zlin)
    (W : V →+ ℂ) {c ε : ℝ} (hc : 0 ≤ c)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal c)
    (hε : 0 < ε) (hε32 : ε < 1 / 32) (hcε : c < Real.sin (Real.pi * ε)) :
    slicingDist C σ.slicing
        (σ.deformedOfSupport hκ hZ hS W hc hW hε hε32 hcε).slicing ≤
      ENNReal.ofReal ε :=
  σ.slicingDist_deformed_le C W _ _ hW _ _ _ hε _ _ _ _

/-- **Existence of the normalized deformation** (BLMNPS, Theorem 12.11; Bayer,
Lemma 5.7).

Let `σ` have the support property with respect to `Q`, with discrete image of
classes, and let `(Q, Zlin)` be normalized. If `u : ker Zlin → ℂ` has norm at most
`c` for `√(-Q)` and `c < sin (π ε)` with `0 < ε < 1/32`, then some stability
condition has central charge `Zlin + u ∘ kerProj Q Zlin` and slicing within `ε`
of that of `σ`. It is `deformedOfSupport`. -/
theorem exists_deformed_of_normalized
    (σ : StabilityCondition.WithClassMap C κ) (hκ : DiscreteTopology (Set.range κ))
    {Zlin : V →ₗ[ℝ] ℂ} (hZ : ∀ x, Zlin x = σ.Z x) {Q : QuadraticForm ℝ V}
    (hQ : IsCompatible Zlin σ.semistableClasses Q) (hN : QuadraticMap.IsNormalized Q Zlin)
    {u : LinearMap.ker Zlin →ₗ[ℝ] ℂ} {c ε : ℝ} (hc : 0 ≤ c)
    (hu : ∀ k, ‖u k‖ ^ 2 ≤ c ^ 2 * -Q k)
    (hε : 0 < ε) (hε32 : ε < 1 / 32) (hcε : c < Real.sin (Real.pi * ε)) :
    ∃ τ : StabilityCondition.WithClassMap C κ,
      τ.Z = (Zlin + u ∘ₗ QuadraticMap.kerProj Q Zlin).toAddMonoidHom ∧
        slicingDist C σ.slicing τ.slicing ≤ ENNReal.ofReal ε := by
  have hS : σ.HasSupportProperty Zlin :=
    HasQuadraticSupportProperty.hasSupportProperty ⟨Q, hQ⟩
  have hW := σ.stabilitySeminorm_le_of_normalized hZ hQ hN hc hu
  exact ⟨σ.deformedOfSupport hκ hZ hS _ hc hW hε hε32 hcε, rfl,
    σ.slicingDist_deformedOfSupport_le hκ hZ hS _ hc hW hε hε32 hcε⟩

end CategoryTheory.Triangulated.StabilityCondition.WithClassMap
