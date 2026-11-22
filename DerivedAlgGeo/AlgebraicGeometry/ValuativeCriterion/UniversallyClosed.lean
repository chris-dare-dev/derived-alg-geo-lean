/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Morphisms.UniversallyClosed
import DerivedAlgGeo.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Discrete valuation rings suffice for universal closedness

Mathlib's valuative criterion tests every valuation ring. Over a locally Noetherian base it is
enough to test discrete valuation rings.

## Main results

* `AlgebraicGeometry.dvr_hasLift_of_isPullback`: the discrete valuation ring existence condition
  is stable under base change.
* `AlgebraicGeometry.specializingMap_of_dvr`: over a locally Noetherian target, a morphism locally
  of finite type with the discrete valuation ring existence condition is specializing (the
  discrete valuation ring form of Stacks 01KE).
* `AlgebraicGeometry.UniversallyClosed.iff_dvr`: Stacks 05JY, (1) ⇔ (4). A morphism of finite type
  over a locally Noetherian base is universally closed if and only if every valuative square over
  it with a discrete valuation ring has a lift.

## Implementation notes

Base changes of `f` need not lie over a Noetherian base, so the discrete valuation ring condition
is not tested against arbitrary base changes. Stacks 05JX reduces universal closedness to
closedness over affine test schemes locally of finite presentation over the base, and those are
locally Noetherian (`LocallyOfFiniteType.isLocallyNoetherian`).

## References

* [Stacks: Tag 05JY](https://stacks.math.columbia.edu/tag/05JY)

## Tags

valuative criterion, discrete valuation ring, universally closed
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The discrete valuation ring existence condition is stable under base change: given a pullback
square, a lift for every discrete valuation ring square over `f` yields one over `f'`. -/
theorem dvr_hasLift_of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : X' ⟶ X} {g' : Y' ⟶ Y} (hP : IsPullback g f' f g')
    (h : ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → sq.commSq.HasLift) :
    ∀ sq : ValuativeCommSq f', IsDiscreteValuationRing sq.R → sq.commSq.HasLift := by
  intro sq hsq
  let sq' : ValuativeCommSq f :=
    { R := sq.R
      K := sq.K
      i₁ := sq.i₁ ≫ g
      i₂ := sq.i₂ ≫ g'
      commSq := ⟨by simp only [Category.assoc, hP.w, reassoc_of% sq.commSq.w]⟩ }
  obtain ⟨l₀, hl₁, hl₂⟩ := (h sq' hsq).exists_lift
  refine ⟨⟨⟨hP.lift l₀ sq.i₂ (by simpa [sq'] using hl₂), ?_, hP.lift_snd _ _ _⟩⟩⟩
  apply hP.hom_ext
  · simpa [sq'] using hl₁
  · simp only [Category.assoc]
    rw [hP.lift_snd]
    exact sq.commSq.w.symm

/-- A morphism locally of finite type over a locally Noetherian target such that every discrete
valuation ring square over it has a lift is specializing. This is the discrete valuation ring form
of Stacks 01KE, `ValuativeCriterion.Existence.specializingMap`. -/
theorem specializingMap_of_dvr {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f]
    (h : ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → sq.commSq.HasLift) :
    SpecializingMap f := by
  intro x' y hxy
  by_cases hne : f x' = y
  · exact ⟨x', specializes_rfl, hne⟩
  obtain ⟨sq, hdvr, hcl, hr⟩ :=
    IsLocallyNoetherian.exists_valuativeCommSq_of_specializes f hxy hne rfl
  obtain ⟨l, hl₁, hl₂⟩ := (h sq hdvr).exists_lift
  obtain ⟨p, hp⟩ : x' ∈ Set.range sq.i₁ := hr ▸ rfl
  refine ⟨l (IsLocalRing.closedPoint sq.R), ?_, ?_⟩
  · rw [← hp, ← hl₁]
    exact (IsLocalRing.specializes_closedPoint _).map l.continuous
  · change (l ≫ f) (IsLocalRing.closedPoint sq.R) = y
    rw [hl₂]
    exact hcl

/-- **Stacks 05JY**, (1) ⇔ (4). A morphism `f : X ⟶ S` of finite type over a locally Noetherian
scheme is universally closed if and only if every valuative square over `f` whose valuation ring
is a discrete valuation ring has a lift.

The lifts exist without any field extension. The forward direction is Mathlib's valuative
criterion, since a discrete valuation ring is a valuation ring. For the converse the proof does
not verify Mathlib's `ValuativeCriterion.Existence` directly: a base change of `f` need not lie
over a Noetherian scheme. It uses Stacks 05JX instead, which tests closedness of base changes
along affine schemes locally of finite presentation over `S`, and these are locally Noetherian.

All three hypotheses are needed:
* `[QuasiCompact f]`: for `∐ₙ Spec k ⟶ 𝔸¹_k`, with `k` infinite, mapping onto distinct closed
  points `aₙ`, every discrete valuation ring square lands over a single `aₙ` and lifts, but the
  image is an infinite set of closed points, which is not closed.
* `[LocallyOfFiniteType f]`: for `Spec ℚ̄ ⟶ Spec ℤ_(p)`, a square with closed point over `(p)`
  would give a discrete valuation of `ℚ̄`, which does not exist, and squares over the generic
  point lift; the image, the generic point, is not closed.
* `[IsLocallyNoetherian S]`: for `V` a valuation ring with value group `ℚ`, no discrete valuation
  ring dominates `V`, so every square for `Spec Frac V ⟶ Spec V` lies over the generic point and
  lifts, but the image is not closed. -/
@[stacks 05JY "(1) ⇔ (4)"]
theorem UniversallyClosed.iff_dvr {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    UniversallyClosed f ↔ ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
      sq.commSq.HasLift := by
  refine ⟨fun hf sq _ ↦ ((UniversallyClosed.eq_valuativeCriterion ▸ hf).1 : _) sq, fun h ↦ ?_⟩
  rw [universallyClosed_iff_isClosedMap_of_locallyOfFinitePresentation]
  intro T _ b _
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian b
  rw [isClosedMap_iff_specializingMap]
  exact specializingMap_of_dvr _ (dvr_hasLift_of_isPullback (IsPullback.of_hasPullback f b) h)

end AlgebraicGeometry
