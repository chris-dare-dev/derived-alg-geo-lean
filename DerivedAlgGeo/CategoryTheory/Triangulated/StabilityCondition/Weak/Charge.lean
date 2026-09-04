/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Charges, and positivity relative to a class datum

A charge condition needs to know two things about a setting: which objects it
speaks about, and which abelian group carries their classes. `ClassDatum` makes
those the parameters, so the abelian and the ambient theories are one structure
at two data rather than two structures with the same fields.

Nothing here is categorical. `ClassDatum O G` quantifies over an arbitrary `O`
and an arbitrary `AddCommGroup G`; the half-planes are subsets of `ℂ`; and the
two structures carry a `G →+ ℂ` and a positivity proof. The instantiations live
with the settings they instantiate at -- `abelianDatum` beside `K₀Ab`,
`heartDatum` beside `K₀`.

## Placement

This file is internal support for the weak stability theory: nothing in it is
triangulated, but every declaration exists to state a charge condition, and
nothing else consumes it. It therefore lives under
`Triangulated/StabilityCondition/Weak/`, beside its only consumer
(`Weak/Foundation/StabilityFunction/Basic.lean`), placed by conceptual ownership
rather than by the weakest vocabulary in its signature, which is only the Tier 2
tie-breaker. It sat at the root of `CategoryTheory/` from #760 until 2026-09-02;
the review of the Mathlib-mesh restructure observed that this promoted
stability-specific support to a subject root it does not own.

The four upper-half-plane facts (`semiClosedUpperHalfPlane`,
`closedUpperHalfPlane`, and their two lemmas) are an upstream candidate for
`Mathlib/Analysis/Complex/UpperHalfPlane/` under the `Complex` namespace. They
stay here for now because the namespace change would rename declarations, and
declaration names are kept stable across moves so that the immutable review
payloads the `exe/RestateHistoricalNames.lean` bridge protects keep resolving.
-/

noncomputable section

universe u v

open Complex Real

namespace CategoryTheory

/-- The semi-closed upper half-plane used for central charges: positive
imaginary part together with the negative real axis. -/
def semiClosedUpperHalfPlane : Set ℂ :=
  {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im = 0 ∧ z.re < 0}

theorem semiClosedUpperHalfPlane_ne_zero {z : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane) : z ≠ 0 := by
  rcases hz with him | ⟨him, hre⟩
  · exact ne_of_apply_ne im him.ne'
  · exact ne_of_apply_ne re hre.ne

/-- The **closed** upper half-plane: the weak condition, which unlike
`semiClosedUpperHalfPlane` contains `0`.  That single difference is the whole of
the weak/strict distinction, and it is why μ-slope stability on a surface is weak
— a skyscraper has zero rank and zero degree, so its μ-charge is `0`. -/
def closedUpperHalfPlane : Set ℂ :=
  {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im = 0 ∧ z.re ≤ 0}

theorem semiClosedUpperHalfPlane_subset_closed :
    semiClosedUpperHalfPlane ⊆ closedUpperHalfPlane :=
  fun _ hz ↦ hz.imp id (fun h ↦ ⟨h.1, h.2.le⟩)

theorem arg_pos_of_mem_semiClosedUpperHalfPlane {z : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane) : 0 < arg z := by
  rcases hz with him | ⟨him, hre⟩
  · refine lt_of_le_of_ne (arg_nonneg_iff.mpr him.le) ?_
    exact fun h => him.ne' (arg_eq_zero_iff.mp h.symm).2
  · have hz : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him)
    rw [hz, arg_ofReal_of_neg hre]
    exact Real.pi_pos

/-- **What a positivity condition needs to know about a category.**

A charge condition speaks about *some* objects (the nonzero ones, or the nonzero
ones lying in a heart) and reads their class in *some* abelian group.  Those two
choices are the only thing that varies between the abelian-category theory and
the ambient/t-structure theory, so they are the parameters.

Making this a parameter rather than baking `K₀Ab` in is what stops the two
theories being two structures with the same fields: they are one structure at two
class data. -/
structure ClassDatum (O : Type*) (G : Type*) [AddCommGroup G] where
  /-- The objects the positivity condition speaks about. -/
  Relevant : O → Prop
  /-- The class of an object. -/
  cl : O → G

variable {O : Type*} {G : Type*} [AddCommGroup G]

/-- A charge is positive for `D` into `P` when every relevant object's class has
charge in `P`. -/
def IsPositive (D : ClassDatum O G) (P : Set ℂ) (Z : G →+ ℂ) : Prop :=
  ∀ E : O, D.Relevant E → Z (D.cl E) ∈ P

/-- **Strict positivity** — the half-plane that excludes `0`. -/
abbrev IsStabilityCharge (D : ClassDatum O G) (Z : G →+ ℂ) : Prop :=
  IsPositive D semiClosedUpperHalfPlane Z

/-- **Weak positivity** — the same with `0` allowed on the real axis. -/
abbrev IsWeakStabilityCharge (D : ClassDatum O G) (Z : G →+ ℂ) : Prop :=
  IsPositive D closedUpperHalfPlane Z

/-- **Strict implies weak**, once and for every class datum. -/
theorem IsStabilityCharge.weak {D : ClassDatum O G} {Z : G →+ ℂ}
    (h : IsStabilityCharge D Z) : IsWeakStabilityCharge D Z :=
  fun E hE ↦ semiClosedUpperHalfPlane_subset_closed (h E hE)

end CategoryTheory
