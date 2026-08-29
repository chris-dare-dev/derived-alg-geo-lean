/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Phase.Order.Characterizations

/-!
# Conditional functoriality of the slicing orders

Remark 3.14(3) of arXiv:2607.28411v1 says the strict and weak orders are
preserved by the paper's pullback and pushforward constructions, when those
constructions are slicings.  This repository does not yet have the geometric
functors or the adjoint-pair API needed to define either construction.

`SlicingOrderPreimageData` isolates the exact categorical interface consumed
by that observation.  An operation on slicings is described objectwise by a
map `obj`; membership in a phase slice and in the strict/weak upper phase
windows is reflected along that same map.  The two order-transport theorems
then follow without importing schemes or manufacturing a fake pullback.

The future `f_sharp` and `f^sharp` constructions can instantiate this data;
until then the result remains explicitly hypothesis-carrying, as required by
destination issue #211 (transferred from source issue #141).
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Objectwise preimage data sufficient to transport both slicing orders.

This is intentionally not a functor or a geometric pullback: it is the exact
hypothesis package that a future pullback or pushforward construction must
discharge. -/
structure SlicingOrderPreimageData (op : Slicing C → Slicing D)
    (obj : D → C) : Prop where
  /-- Phase-slice membership is computed on the chosen source object. -/
  semistable_iff : ∀ (s : Slicing C) (phi : ℝ) (E : D),
    (op s).P phi E ↔ s.P phi (obj E)
  /-- The strict upper phase window is computed on the same source object. -/
  ltProp_iff : ∀ (s : Slicing C) (phi : ℝ) (E : D),
    (op s).ltProp D phi E ↔ s.ltProp C phi (obj E)
  /-- The weak upper phase window is computed on the same source object. -/
  leProp_iff : ∀ (s : Slicing C) (phi : ℝ) (E : D),
    (op s).leProp D phi E ↔ s.leProp C phi (obj E)

/-- Any slicing operation satisfying the preimage interface preserves the
strict order.  This is the hypothesis-carrying form of the strict
pullback/pushforward clause in Remark 3.14(3). -/
theorem SlicingOrderPreimageData.precedes {op : Slicing C → Slicing D}
    {obj : D → C} (h : SlicingOrderPreimageData op obj)
    {s t : Slicing C} (hst : s.Precedes C t) :
    (op s).Precedes D (op t) := by
  intro phi E hE
  apply (h.ltProp_iff t phi E).mpr
  exact hst phi (obj E) ((h.semistable_iff s phi E).mp hE)

/-- Any slicing operation satisfying the preimage interface preserves the
weak order.  This is the hypothesis-carrying form of the weak
pullback/pushforward clause in Remark 3.14(3). -/
theorem SlicingOrderPreimageData.precedesWeak {op : Slicing C → Slicing D}
    {obj : D → C} (h : SlicingOrderPreimageData op obj)
    {s t : Slicing C} (hst : s.PrecedesWeak C t) :
    (op s).PrecedesWeak D (op t) := by
  intro phi E hE
  apply (h.leProp_iff t phi E).mpr
  exact hst phi (obj E) ((h.semistable_iff s phi E).mp hE)

/-- Source-facing strict pushforward wrapper.  No pushforward is constructed:
the caller supplies its preimage data explicitly. -/
theorem Slicing.Precedes.pushforward_of_preimage
    (op : Slicing C → Slicing D) (obj : D → C)
    (h : SlicingOrderPreimageData op obj) {s t : Slicing C}
    (hst : s.Precedes C t) : (op s).Precedes D (op t) :=
  h.precedes hst

/-- Source-facing weak pushforward wrapper. -/
theorem Slicing.PrecedesWeak.pushforward_of_preimage
    (op : Slicing C → Slicing D) (obj : D → C)
    (h : SlicingOrderPreimageData op obj) {s t : Slicing C}
    (hst : s.PrecedesWeak C t) : (op s).PrecedesWeak D (op t) :=
  h.precedesWeak hst

/-- Source-facing strict pullback wrapper.  It is deliberately a second name
for the same abstract interface: which geometric adjoint computes `obj` is a
fact for the future pullback construction, not for the slicing-order layer. -/
theorem Slicing.Precedes.pullback_of_preimage
    (op : Slicing C → Slicing D) (obj : D → C)
    (h : SlicingOrderPreimageData op obj) {s t : Slicing C}
    (hst : s.Precedes C t) : (op s).Precedes D (op t) :=
  h.precedes hst

/-- Source-facing weak pullback wrapper. -/
theorem Slicing.PrecedesWeak.pullback_of_preimage
    (op : Slicing C → Slicing D) (obj : D → C)
    (h : SlicingOrderPreimageData op obj) {s t : Slicing C}
    (hst : s.PrecedesWeak C t) : (op s).PrecedesWeak D (op t) :=
  h.precedesWeak hst

end CategoryTheory.Triangulated
