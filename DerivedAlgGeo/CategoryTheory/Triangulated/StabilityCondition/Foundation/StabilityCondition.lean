/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.

Portions adapted from mattrobball/BridgelandStability, revision 9e48f23
(Apache-2.0, Copyright (c) 2026 Mathlib Contributors); see LICENSE.md.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.IntervalCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.PreStabilityCondition

/-!
# Local finiteness and stability conditions

This file adds the locally-finite refinement of the owner-controlled
pre-stability API. The radius is normalized to be less than `1/2`, so every
window has width at most one.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ]

/-- A slicing is locally finite if one uniform thin window around every phase
has finite length with respect to admissible subobjects. -/
structure Slicing.IsLocallyFinite (s : Slicing C) : Prop where
  /-- A uniform normalized radius with finite-length interval categories. -/
  intervalFinite : ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∀ t : ℝ,
    ∀ E : s.IntervalCat C (t - η) (t + η), s.IsFiniteLength C E

namespace StabilityCondition

/-- A stability condition with a chosen class map. -/
structure WithClassMap (v : K₀ C →+ Λ)
    extends PreStabilityCondition.WithClassMap C v where
  /-- The underlying slicing is locally finite. -/
  locallyFinite : slicing.IsLocallyFinite C

namespace WithClassMap

variable {C}

@[ext]
theorem ext {v : K₀ C →+ Λ} {σ τ : WithClassMap C v}
    (hslicing : σ.slicing = τ.slicing) (hZ : σ.Z = τ.Z) : σ = τ := by
  have hpre : σ.toWithClassMap = τ.toWithClassMap :=
    PreStabilityCondition.WithClassMap.ext hslicing hZ
  rcases σ with ⟨σpre, hlfσ⟩
  rcases τ with ⟨τpre, hlfτ⟩
  cases hpre
  cases Subsingleton.elim hlfσ hlfτ
  rfl

end WithClassMap

end StabilityCondition

/-- A stability condition with the identity class map. -/
abbrev StabilityCondition :=
  StabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C))

theorem stabilityCondition_compat_apply (σ : StabilityCondition C)
    (φ : ℝ) (E : C) (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    ∃ m : ℝ, 0 < m ∧
      σ.Z (K₀.of C E) = (m : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I) := by
  simpa [PreStabilityCondition.WithClassMap.charge_def, classOf_id] using
    σ.compat φ E hP hE

end CategoryTheory.Triangulated
