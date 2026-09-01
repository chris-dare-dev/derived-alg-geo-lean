/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Metric.Mass.Uniqueness
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Basic

/-!
# Harder--Narasimhan mass for weak prestability conditions

The mass-uniqueness induction of `Metric/Mass/Uniqueness.lean` is stated for a
bare carrier `(s : Slicing C, Z : K₀ C →+ ℂ)`, precisely because it never
consults a compatibility ray.  A weak prestability condition carries both — a
slicing and a charge whose ray is closed at integer phases — so its HN mass
theory is the general one, instantiated.  This file makes those instances the
public weak API: the mass of a weak HN filtration is independent of the
filtration, the choice-free envelope equals every filtration's finite sum, and
the envelope is finite.

What does **not** transport is positivity: a nonzero weak semistable object of
integer phase may have charge zero, so `stabilityMass_pos` has no weak
analogue, and the zero-mass locus is exactly the `A⁰` direction of
Definition 14.3 rather than the zero objects.  Nothing in this file claims
otherwise.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated
open scoped ENNReal

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
variable {Λ : Type*} [AddCommGroup Λ] {v : K₀ C →+ Λ}
variable (W : WeakPreStabilityCondition (C := C) v)

/-- The finite mass sum of one HN filtration for the slicing of a weak
prestability condition: the general `classMass` at the composite charge
`W.Z.comp v`. -/
def hnMass {E : C} (F : HNFiltration C W.slicing.P E) : ℝ≥0∞ :=
  F.classMass (W.Z.comp v)

/-- The choice-free weak HN mass envelope of an object. -/
def stabilityMass (E : C) : ℝ≥0∞ :=
  W.slicing.classMass (W.Z.comp v) E

/-- **Weak HN mass is independent of the chosen HN filtration.**  The head–tail
octahedral induction never needs the charge of a semistable factor to be
nonzero, so it applies verbatim to the closed compatibility ray. -/
theorem hnMass_eq_hnMass {E : C} (F G : HNFiltration C W.slicing.P E) :
    W.hnMass F = W.hnMass G :=
  F.classMass_eq_classMass (W.Z.comp v) G

/-- The weak mass envelope is the finite mass sum of every HN filtration. -/
theorem stabilityMass_eq_hnMass {E : C} (F : HNFiltration C W.slicing.P E) :
    W.stabilityMass E = W.hnMass F :=
  Slicing.classMass_eq_classMass W.slicing (W.Z.comp v) F

/-- **The weak mass envelope is always finite.**  Finiteness needs only that
some HN filtration exists and that each filtration's mass is a finite sum —
never positivity of the summands, which is what fails weakly. -/
theorem stabilityMass_ne_top (E : C) : W.stabilityMass E ≠ ⊤ :=
  Slicing.classMass_ne_top W.slicing (W.Z.comp v) E

end

end CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition
