/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.

Portions adapted from mattrobball/BridgelandStability, revision 9e48f23
(Apache-2.0, Copyright (c) 2026 Mathlib Contributors); see LICENSE.md.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Basic.Definitions
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Owner-authored pre-stability conditions

A pre-stability condition consists of a slicing and a central charge whose
value on every nonzero semistable object lies on the positive ray determined
by its phase. Local finiteness is deliberately deferred to the next ownership
slice.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped BigOperators

universe u v u'

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ]

namespace PreStabilityCondition

/-- A pre-stability condition whose central charge factors through a chosen
class map `v : K₀ C → Λ`.

Ordinary prestability is a strict refinement of weak prestability.  The named
parent projection makes that relationship part of the Lean type rather than a
downstream compatibility adapter. -/
structure WithClassMap (v : K₀ C →+ Λ)
    extends toWeak : WeakStabilityCondition.WeakPreStabilityCondition (C := C) v where
  /-- A nonzero semistable object's charge lies on its positive phase ray. -/
  compatible : ∀ φ E, slicing.P φ E → ¬IsZero E →
    ∃ m : ℝ, 0 < m ∧
      Z (v (K₀.of C E)) = (m : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I)

namespace WithClassMap

variable {C}

/-- Build ordinary prestability from its strict compatibility proof.  The
weak compatibility field is derived canonically from strict positivity. -/
def ofStrict {v : K₀ C →+ Λ} (slicing : Slicing C) (Z : Λ →+ ℂ)
    (compatible : ∀ φ E, slicing.P φ E → ¬IsZero E →
      ∃ m : ℝ, 0 < m ∧
        Z (v (K₀.of C E)) = (m : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I)) :
    WithClassMap C v where
  toWeak :=
    { slicing := slicing
      Z := Z
      compat' := by
        intro φ E hP hE
        obtain ⟨m, hm, heq⟩ := compatible φ E hP hE
        exact ⟨m, hm.le, fun _ ↦ hm, heq⟩ }
  compatible := compatible

/-- The central charge evaluated on the class of an object. -/
abbrev charge {v : K₀ C →+ Λ} (σ : WithClassMap C v) (E : C) : ℂ :=
  σ.Z (classOf C v E)

theorem charge_def {v : K₀ C →+ Λ} (σ : WithClassMap C v) (E : C) :
    σ.charge E = σ.Z (classOf C v E) := rfl

/-- Compatibility expressed through `charge`. -/
theorem compat {v : K₀ C →+ Λ} (σ : WithClassMap C v)
    (φ : ℝ) (E : C) (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    ∃ m : ℝ, 0 < m ∧
      σ.charge E = (m : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I) :=
  σ.compatible φ E hP hE

@[simp]
theorem charge_isZero {v : K₀ C →+ Λ} (σ : WithClassMap C v)
    {E : C} (hE : IsZero E) : σ.charge E = 0 := by
  simp [charge_def, classOf_isZero C v hE]

theorem charge_congr {v : K₀ C →+ Λ} {σ τ : WithClassMap C v}
    (h : σ.Z = τ.Z) (E : C) : σ.charge E = τ.charge E := by
  simp only [charge_def, h]

theorem charge_postnikovTower_eq_sum {v : K₀ C →+ Λ}
    (σ : WithClassMap C v) {E : C} (P : PostnikovTower C E) :
    σ.charge E = ∑ i : Fin P.n, σ.charge (P.factor i) := by
  simp only [charge_def, classOf_postnikovTower_eq_sum C v P, map_sum]

@[ext]
theorem ext {v : K₀ C →+ Λ} {σ τ : WithClassMap C v}
    (hslicing : σ.slicing = τ.slicing) (hZ : σ.Z = τ.Z) : σ = τ := by
  rcases σ with ⟨⟨sσ, Zσ, wσ⟩, cσ⟩
  rcases τ with ⟨⟨sτ, Zτ, wτ⟩, cτ⟩
  simp at hslicing hZ
  cases hslicing
  cases hZ
  cases Subsingleton.elim wσ wτ
  cases Subsingleton.elim cσ cτ
  rfl

end WithClassMap

end PreStabilityCondition

/-- A pre-stability condition with the identity class map. -/
abbrev PreStabilityCondition :=
  PreStabilityCondition.WithClassMap C (AddMonoidHom.id (K₀ C))

theorem preStabilityCondition_compat_apply (σ : PreStabilityCondition C)
    (φ : ℝ) (E : C) (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    ∃ m : ℝ, 0 < m ∧
      σ.Z (K₀.of C E) = (m : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I) := by
  simpa [PreStabilityCondition.WithClassMap.charge_def, classOf_id] using
    σ.compat φ E hP hE

end CategoryTheory.Triangulated
