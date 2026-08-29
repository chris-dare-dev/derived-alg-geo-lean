/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.Splitting
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.TorsionPair.Basic

/-!
# The torsion pair of an abelian stability function at a phase cutoff

For a stability function `Z` on an abelian category with the Harder–Narasimhan
property, and a number `β`, the two classes of `Foundation/StabilityFunction/
Cutoff.lean`

```
T β = {E | every HN phase of E exceeds β}      F β = {E | every HN phase is at most β}
```

are a `TorsionPair`.  Both axioms are already proved:

* `hom_eq_zero` is `hom_eq_zero_of_mem_hnTors_of_mem_hnFree` — the image of a
  map is a quotient of the source and a subobject of the target, so the
  monotonicity of `PhaseMonotone.lean` traps its phases in the empty interval
  `(β, β]`;
* `exists_shortExact` is `exists_shortExact_hnTors_hnFree` — the HN chain cut
  at the index where its phases cross `β`.

## Relation to the slicing torsion pair

`TorsionPair/Slope.lean` builds the same display (14.1) pair on the heart of a
**slicing** in a triangulated category, from the slicing's own phase-ordered
vanishing.  This file is the **abelian** statement, for an object-level
stability function and its own HN filtrations, which is the form Bridgeland's
§6 uses on `Coh X`: with the charge `-degree + i·rank` of `Slope.lean`, `T β`
and `F β` are the μ-slope classes `{μ⁻ > β}` and `{μ⁺ ≤ β}`.  Neither pair is
derived from the other here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Triangulated.Tilting

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace StabilityFunction

/-- The torsion class at a cutoff, as an `ObjectProperty`. -/
def hnTorsProperty (Z : StabilityFunction A) (β : ℝ) : ObjectProperty A :=
  fun E => E ∈ hnTors Z β

/-- The torsion-free class at a cutoff, as an `ObjectProperty`. -/
def hnFreeProperty (Z : StabilityFunction A) (β : ℝ) : ObjectProperty A :=
  fun E => E ∈ hnFree Z β

instance hnTorsProperty_isClosedUnderIsomorphisms (Z : StabilityFunction A)
    (β : ℝ) : (hnTorsProperty Z β).IsClosedUnderIsomorphisms :=
  ⟨fun e h => hnTors_of_iso e h⟩

instance hnFreeProperty_isClosedUnderIsomorphisms (Z : StabilityFunction A)
    (β : ℝ) : (hnFreeProperty Z β).IsClosedUnderIsomorphisms :=
  ⟨fun e h => hnFree_of_iso e h⟩

/-- **The two classes at a phase cutoff are a torsion pair.** -/
def hnTorsionPair (Z : StabilityFunction A) (β : ℝ) (hHN : Z.HasHNProperty) :
    TorsionPair A where
  tors := hnTorsProperty Z β
  free := hnFreeProperty Z β
  hom_eq_zero _ _ hX hY f := hom_eq_zero_of_mem_hnTors_of_mem_hnFree hHN hX hY f
  exists_shortExact E := exists_shortExact_hnTors_hnFree hHN (β := β) E

@[simp]
theorem hnTorsionPair_tors (Z : StabilityFunction A) (β : ℝ)
    (hHN : Z.HasHNProperty) :
    (hnTorsionPair Z β hHN).tors = hnTorsProperty Z β :=
  rfl

@[simp]
theorem hnTorsionPair_free (Z : StabilityFunction A) (β : ℝ)
    (hHN : Z.HasHNProperty) :
    (hnTorsionPair Z β hHN).free = hnFreeProperty Z β :=
  rfl

end StabilityFunction

end CategoryTheory.Triangulated
