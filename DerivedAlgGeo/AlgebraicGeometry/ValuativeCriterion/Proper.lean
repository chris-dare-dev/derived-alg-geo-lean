/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ValuativeCriterion
import DerivedAlgGeo.AlgebraicGeometry.ValuativeCriterion.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Discrete valuation rings suffice for properness

Over a locally Noetherian base, a morphism of finite type is proper if and only if every
valuative square over it with a discrete valuation ring has exactly one lift.

## Main results

* `AlgebraicGeometry.IsProper.iff_dvr`: Stacks 0208, (1) ⇔ (3).

## Implementation notes

Stacks proves (4) ⇒ (1) by Chow's lemma (Tag 0200) and derives the criterion for discrete
valuation rings from it. Here the criterion is obtained from separatedness
(`AlgebraicGeometry.IsSeparated.iff_dvr`, Stacks 0207) and universal closedness
(`AlgebraicGeometry.UniversallyClosed.iff_dvr`, Stacks 05JY), because Mathlib's `IsProper` is
separated, universally closed and locally of finite type. Condition (4), which tests only squares
at generic points of irreducible components, is not proved.

## References

* [Stacks: Tag 0208](https://stacks.math.columbia.edu/tag/0208)

## Tags

valuative criterion, discrete valuation ring, proper morphism
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Stacks 0208**, (1) ⇔ (3). A morphism `f : X ⟶ S` of finite type over a locally Noetherian
scheme is proper if and only if every valuative square over `f` whose valuation ring is a discrete
valuation ring has exactly one lift.

This is proved from Stacks 0207 (`IsSeparated.iff_dvr`) and Stacks 05JY
(`UniversallyClosed.iff_dvr`), not by Stacks' route through Chow's lemma (Tag 0200). Stacks 0208
(4), the form that tests only squares at generic points of irreducible components, is not proved
here, since it needs Chow's lemma.

The hypotheses are those of `UniversallyClosed.iff_dvr`, which are needed there, together with
`[LocallyOfFiniteType f]` of `IsSeparated.iff_dvr`. -/
@[stacks 0208 "(1) ⇔ (3)"]
theorem IsProper.iff_dvr {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    IsProper f ↔ ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
      Nonempty (Unique sq.commSq.LiftStruct) := by
  constructor
  · intro hf
    have h : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme) f := by
      rw [← IsProper.eq_valuativeCriterion]
      exact hf
    exact fun sq _ ↦ h.1.1.1 sq
  · intro h
    have hu : ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
        Subsingleton sq.commSq.LiftStruct := fun sq hsq ↦ by
      obtain ⟨u⟩ := h sq hsq
      infer_instance
    have he : ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → sq.commSq.HasLift :=
      fun sq hsq ↦ by
        obtain ⟨u⟩ := h sq hsq
        exact ⟨⟨default⟩⟩
    have : IsSeparated f := (IsSeparated.iff_dvr f).mpr hu
    have : UniversallyClosed f := (UniversallyClosed.iff_dvr f).mpr he
    exact {}

end AlgebraicGeometry
