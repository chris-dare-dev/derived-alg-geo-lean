/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.DeformedShift

/-!
# Triangulated closure of owner deformed phase cuts

The owner deformed cuts are extension closed by construction.  Their shift
symmetry upgrades this to the rotated closure properties needed for the
prospective deformed t-structure.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace StabilityCondition.WithClassMap

/-- The cut `Q(>t)` is closed under forward shift without changing `t`. -/
theorem deformedGtPred_shift_one_same
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} {X : C} (hX : σ.deformedGtPred C W hr0 hr1 hW ε t X) :
    σ.deformedGtPred C W hr0 hr1 hW ε t (X⟦(1 : ℤ)⟧) :=
  σ.deformedGtPred_anti C W hr0 hr1 hW (show t ≤ t + 1 by linarith) _
    (σ.deformedGtPred_shift_one C W hr0 hr1 hW hX)

/-- The cut `Q(≤t)` is closed under backward shift without changing `t`. -/
theorem deformedLePred_shift_neg_one_same
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} {X : C} (hX : σ.deformedLePred C W hr0 hr1 hW ε t X) :
    σ.deformedLePred C W hr0 hr1 hW ε t (X⟦(-1 : ℤ)⟧) :=
  σ.deformedLePred_mono C W hr0 hr1 hW (show t - 1 ≤ t by linarith) _
    (σ.deformedLePred_shift_neg_one C W hr0 hr1 hW hX)

/-- The cut `Q(<t)` is closed under backward shift without changing `t`. -/
theorem deformedLtPred_shift_neg_one_same
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} {X : C} (hX : σ.deformedLtPred C W hr0 hr1 hW ε t X) :
    σ.deformedLtPred C W hr0 hr1 hW ε t (X⟦(-1 : ℤ)⟧) :=
  σ.deformedLtPred_mono C W hr0 hr1 hW (show t - 1 ≤ t by linarith) _
    (σ.deformedLtPred_shift_neg_one C W hr0 hr1 hW hX)

/-- `Q(>t)` contains the third vertex when it contains the first two. -/
theorem deformedGtPred_of_triangle_obj₃
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} {X S Y : C} {f : X ⟶ S} {g : S ⟶ Y}
    {h : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (hX : σ.deformedGtPred C W hr0 hr1 hW ε t X)
    (hS : σ.deformedGtPred C W hr0 hr1 hW ε t S) :
    σ.deformedGtPred C W hr0 hr1 hW ε t Y :=
  .ext (rot_of_distTriang _ hT) hS
    (σ.deformedGtPred_shift_one_same C W hr0 hr1 hW hX)

/-- `Q(≤t)` contains the first vertex when it contains the last two. -/
theorem deformedLePred_of_triangle_obj₁
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} {X S Y : C} {f : X ⟶ S} {g : S ⟶ Y}
    {h : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (hS : σ.deformedLePred C W hr0 hr1 hW ε t S)
    (hY : σ.deformedLePred C W hr0 hr1 hW ε t Y) :
    σ.deformedLePred C W hr0 hr1 hW ε t X :=
  .ext (inv_rot_of_distTriang _ hT)
    (σ.deformedLePred_shift_neg_one_same C W hr0 hr1 hW hY) hS

/-- `Q(<t)` contains the first vertex when it contains the last two. -/
theorem deformedLtPred_of_triangle_obj₁
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} {X S Y : C} {f : X ⟶ S} {g : S ⟶ Y}
    {h : Y ⟶ X⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (hS : σ.deformedLtPred C W hr0 hr1 hW ε t S)
    (hY : σ.deformedLtPred C W hr0 hr1 hW ε t Y) :
    σ.deformedLtPred C W hr0 hr1 hW ε t X :=
  .ext (inv_rot_of_distTriang _ hT)
    (σ.deformedLtPred_shift_neg_one_same C W hr0 hr1 hW hY) hS

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
