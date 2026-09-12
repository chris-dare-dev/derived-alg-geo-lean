/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakHarderNarasimhan
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakSlopeTop

/-!
# Transporting weak HN filtrations across the same slope order

Two weak slope data may use different numerical normalizations while inducing
the same order on objects.  Their semistable objects and HN filtrations are
then the same.  This file records that fact without requiring equality of the
underlying rank and degree homomorphisms.

The motivating example is a polarized surface: the leading two Hilbert
coefficients differ from numerical rank and divisor degree by a positive
scaling and an affine rank term.  That changes the displayed finite slope but
not its order, and keeps rank-zero slope equal to `⊤`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace WeakSlopeData

/-- Two weak slope data define the same preorder on slopes of objects. -/
structure SameSlopeOrder (D E : WeakSlopeData A) : Prop where
  /-- The two slope comparisons agree on every pair of objects. -/
  le_iff : ∀ X Y : A, D.topSlope X ≤ D.topSlope Y ↔ E.topSlope X ≤ E.topSlope Y

namespace SameSlopeOrder

variable {D E : WeakSlopeData A}

/-- Strict slope comparisons agree as well. -/
theorem lt_iff (h : SameSlopeOrder D E) (X Y : A) :
    D.topSlope X < D.topSlope Y ↔ E.topSlope X < E.topSlope Y := by
  simpa only [lt_iff_not_ge] using
    not_congr (WeakSlopeData.SameSlopeOrder.le_iff h Y X)

/-- The two weak slope data have exactly the same semistable objects. -/
theorem isSemistable_iff (h : SameSlopeOrder D E) (X : A) :
    D.toWeakStabilityFunction.IsSemistable X ↔
      E.toWeakStabilityFunction.IsSemistable X := by
  constructor
  · rintro ⟨hX, hs⟩
    exact ⟨hX, fun B hB =>
      (WeakSlopeData.SameSlopeOrder.le_iff h (B : A) X).mp (hs B hB)⟩
  · rintro ⟨hX, hs⟩
    exact ⟨hX, fun B hB =>
      (WeakSlopeData.SameSlopeOrder.le_iff h (B : A) X).mpr (hs B hB)⟩

end SameSlopeOrder

end WeakSlopeData

namespace AbelianWeakHNFiltration

variable {D E : WeakSlopeData A} {X : A}

/-- Reinterpret an HN filtration using weak slope data with the same slope
order.  The subobject chain is unchanged; only its intrinsic slope labels are
recomputed. -/
def changeSlopeOrder
    (F : AbelianWeakHNFiltration D.toWeakStabilityFunction X)
    (h : WeakSlopeData.SameSlopeOrder D E) :
    AbelianWeakHNFiltration E.toWeakStabilityFunction X where
  n := F.n
  nonempty := F.nonempty
  chain := F.chain
  chain_strictMono := F.chain_strictMono
  chain_bot := F.chain_bot
  chain_top := F.chain_top
  μ := fun j => E.topSlope (F.factor j)
  μ_anti := by
    intro i j hij
    apply (WeakSlopeData.SameSlopeOrder.lt_iff h (F.factor j) (F.factor i)).mp
    change D.toWeakStabilityFunction.slope (F.factor j) <
      D.toWeakStabilityFunction.slope (F.factor i)
    rw [F.factor_slope i, F.factor_slope j]
    exact F.μ_anti hij
  factor_slope := fun _ => rfl
  factor_semistable := fun j =>
    (WeakSlopeData.SameSlopeOrder.isSemistable_iff h (F.factor j)).mp
      (F.factor_semistable j)

end AbelianWeakHNFiltration

namespace WeakSlopeData.SameSlopeOrder

variable {D E : WeakSlopeData A}

/-- The HN property depends only on the order induced by the honest slope. -/
theorem hasHNProperty (h : WeakSlopeData.SameSlopeOrder D E)
    (hD : D.toWeakStabilityFunction.HasHNProperty) :
    E.toWeakStabilityFunction.HasHNProperty := by
  intro X hX
  obtain ⟨F⟩ := hD X hX
  exact ⟨F.changeSlopeOrder h⟩

end WeakSlopeData.SameSlopeOrder

end CategoryTheory.Triangulated
