/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Basic.Definitions
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.StabilityCondition

/-!
# Ordinary prestability forgets to weak prestability

The open compatibility ray of an ordinary prestability condition lies in the
closed ray required by weak prestability. Keeping this adapter in the strong
child makes the dependency direction explicit.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated Complex

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type*} [AddCommGroup Λ]

namespace WeakPreStabilityCondition

/-- Ordinary prestability embeds into weak prestability, preserving the
slicing and charge definitionally. -/
def ofPre {v : K₀ C →+ Λ} (σ : PreStabilityCondition.WithClassMap C v) :
    WeakPreStabilityCondition v where
  slicing := σ.slicing
  Z := σ.Z
  compat' φ E hP hE := by
    obtain ⟨m, hm, heq⟩ := σ.compatible φ E hP hE
    exact ⟨m, hm.le, fun _ => hm, heq⟩

@[simp]
theorem ofPre_slicing {v : K₀ C →+ Λ}
    (σ : PreStabilityCondition.WithClassMap C v) :
    (ofPre σ).slicing = σ.slicing := rfl

@[simp]
theorem ofPre_Z {v : K₀ C →+ Λ} (σ : PreStabilityCondition.WithClassMap C v) :
    (ofPre σ).Z = σ.Z := rfl

end WeakPreStabilityCondition

end CategoryTheory.Triangulated.WeakStabilityCondition

namespace CategoryTheory.Triangulated.StabilityCondition.WithClassMap

open CategoryTheory Limits Pretriangulated Complex

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type*} [AddCommGroup Λ]

/-- A Bridgeland stability condition canonically exposes its weak stability
data by forgetting local finiteness and weakening the charge-ray inequality. -/
def toWeak {v : K₀ C →+ Λ} (σ : WithClassMap C v) :
    WeakStabilityCondition.WeakPreStabilityCondition v :=
  WeakStabilityCondition.WeakPreStabilityCondition.ofPre σ.toWithClassMap

@[simp]
theorem toWeak_slicing {v : K₀ C →+ Λ} (σ : WithClassMap C v) :
    σ.toWeak.slicing = σ.slicing := rfl

@[simp]
theorem toWeak_Z {v : K₀ C →+ Λ} (σ : WithClassMap C v) :
    σ.toWeak.Z = σ.Z := rfl

end CategoryTheory.Triangulated.StabilityCondition.WithClassMap
