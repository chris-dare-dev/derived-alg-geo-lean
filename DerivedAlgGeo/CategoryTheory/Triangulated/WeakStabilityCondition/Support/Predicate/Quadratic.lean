/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Support.Predicate.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Genuine quadratic forms for the support property

The basic support layer is intentionally stated for continuous degree-two
homogeneous functions.  The source definitions in §§18 and 21 of
arXiv:1902.08184v4 instead quantify over an actual quadratic form.  This file
supplies that stronger, bundled interface and proves that it implies the
existing norm estimate.

No converse is asserted here.  Over an arbitrary normed real vector space the
explicit witness built from the norm in `Support.Basic` need not be a quadratic
form.  That asymmetry is deliberate and remains visible in the API.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Support

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Every quadratic form on a finite-dimensional real normed space is a
continuous degree-two homogeneous function.

Continuity is obtained from the polar bilinear form.  Finite dimensionality is
used precisely to turn that algebraic bilinear map into a continuous one. -/
theorem quadraticForm_isHomogTwo (Q : QuadraticForm ℝ V) :
    IsHomogTwo (Q : V → ℝ) := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := Q.polarBilin.toContinuousBilinearMap
  have hB : Continuous fun x : V => B x x :=
    B.continuous₂.comp₂ continuous_id continuous_id
  refine ⟨?_, ?_⟩
  · have hfun : (fun x : V => Q x) = fun x : V => (2 : ℝ)⁻¹ * B x x := by
      funext x
      have hpolar : B x x = 2 * Q x := by
        rw [show B x x = Q.polarBilin x x by rfl,
          QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
        simp
      rw [hpolar]
      ring
    change Continuous fun x : V => Q x
    rw [hfun]
    exact continuous_const.mul hB
  · intro a x
    rw [Q.map_smul]
    simp only [smul_eq_mul]
    ring

/-- Compatibility with a genuine quadratic form: nonnegative on the selected
classes and negative definite on the kernel of the charge. -/
def HasQuadraticSupportProperty (Z : V →ₗ[ℝ] W) (S : Set V) : Prop :=
  ∃ Q : QuadraticForm ℝ V, IsCompatible Z S Q

/-- A genuine quadratic support form yields the norm-bound formulation of the
support property. -/
theorem HasQuadraticSupportProperty.hasSupportProperty
    {Z : V →ₗ[ℝ] W} {S : Set V}
    (h : HasQuadraticSupportProperty Z S) : HasSupportProperty Z S := by
  obtain ⟨Q, hQ⟩ := h
  exact hasSupportProperty_of_isCompatible (quadraticForm_isHomogTwo Q) hQ

omit [FiniteDimensional ℝ V] in
/-- The genuine quadratic predicate is monotone in the selected locus. -/
theorem HasQuadraticSupportProperty.mono
    {Z : V →ₗ[ℝ] W} {S S' : Set V}
    (h : HasQuadraticSupportProperty Z S) (hS : S' ⊆ S) :
    HasQuadraticSupportProperty Z S' := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q, ⟨fun x hx => hQ.nonneg_of_mem x (hS hx), hQ.neg_of_ker⟩⟩

end CategoryTheory.Triangulated.StabilityCondition.Support
