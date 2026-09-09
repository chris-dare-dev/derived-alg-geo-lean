/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.BMT
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Threefold

/-!
# Transporting a polarised threefold class to the `(α, β)` plane

`Walls/Threefold/Basic.lean` does its charge arithmetic on `NumClass`, a
quadruple of reals, and says of it: "It is **not** `ch(E)` for a sheaf `E`."
This file supplies the map that makes it one, exactly as `WallTransport.lean`
does in the surface case, and on the same side of the geometry boundary.

## The rank slot carries `∫H³`

Matching the surface file, where it carries `∫H²`.  The four coordinates are

```text
∫H³·ch₀,   ∫H²·ch₁,   ∫H·ch₂,   ∫ch₃,
```

and the first is weighted because that is what the charge polynomial requires.

## The compressed twist is the ring twist

`betaTwist_toNumClass` is the theorem the file turns on: the four-coordinate
`betaTwist` of `Walls/Threefold/` agrees with the twisted degrees `degH1Beta`,
`degH2Beta` and `deg3Beta` that `BMT.lean` reads off `chBetaComp`.  It is proved
by expanding the truncated exponential in each of codimensions one, two and
three; the three helper lemmas below are that expansion and are the only real
computation here.

With it, `Q_toNumClass` and `nu_toNumClass` identify the compressed
Bayer--Macrì--Toda quantity and tilt slope with the ones `BMT.lean` already
defines, so there is one `Q` in the library rather than two.

## The conjecture is transported, not proved

`Q_toNumClass_nonneg` takes `BMTData` — supplied data that is **false for some
threefolds**, see `BMT.lean` — and restates its inequality on the transported
class.  Nothing here makes it more true than it was.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition

universe u v

namespace AlgebraicGeometry.Numerical

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]

namespace Threefold

variable (V : NumericalVarietyData 3 A N) (P : Polarization V.ring)

/-! ### The twisted degrees, expanded

The three lemmas below expand the truncated exponential `e^{-βH}` in
codimensions one, two and three.  They are the only real computation in the
file; everything after them is bookkeeping. -/

private theorem tc0 (β : ℚ) : twistCoeff β 0 = 1 := by
  simp [twistCoeff]

private theorem tc1 (β : ℚ) : twistCoeff β 1 = -β := by
  simp [twistCoeff]

private theorem tc2 (β : ℚ) : twistCoeff β 2 = β ^ 2 / 2 := by
  rw [twistCoeff]
  norm_num [Nat.factorial]

private theorem tc3 (β : ℚ) : twistCoeff β 3 = -(β ^ 3) / 6 := by
  rw [twistCoeff]
  norm_num [Nat.factorial]
  ring

/-- `∫H²·ch₁^β = ∫H²ch₁ − β·∫H³ch₀`. -/
theorem degH1Beta_eq (β : ℚ) (E : N) :
    degH1Beta V P β E =
      V.ring.degree (V.chComp E 1 * P.cls ^ 2)
        - β * (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ)) := by
  rw [degH1Beta, chBetaComp_eq, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  simp only [Nat.sub_self, Nat.sub_zero, tc0, tc1, V.chComp_zero, map_one, one_mul]
  rw [add_mul, map_add]
  rw [show algebraMap ℚ A (-β) * algebraMap ℚ A ((V.rank E : ℤ) : ℚ) * P.cls ^ 1 * P.cls ^ 2
      = algebraMap ℚ A (-β * ((V.rank E : ℤ) : ℚ)) * P.cls ^ 3 from by
    rw [map_mul]; ring]
  rw [show V.chComp E 1 * P.cls ^ 0 * P.cls ^ 2 = V.chComp E 1 * P.cls ^ 2 from by ring]
  rw [NumericalRingData.degree_algebraMap_mul]
  ring

/-- `∫H·ch₂^β = ∫H·ch₂ − β·∫H²ch₁ + (β²/2)·∫H³ch₀`. -/
theorem degH2Beta_eq (β : ℚ) (E : N) :
    degH2Beta V P β E =
      V.ring.degree (V.chComp E 2 * P.cls)
        - β * V.ring.degree (V.chComp E 1 * P.cls ^ 2)
        + β ^ 2 / 2 * (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ)) := by
  rw [degH2Beta, chBetaComp_eq, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Nat.sub_self, Nat.sub_zero, show (2 : ℕ) - 1 = 1 from rfl, tc0, tc1, tc2,
    V.chComp_zero, map_one, one_mul]
  rw [add_mul, add_mul, map_add, map_add]
  rw [show algebraMap ℚ A (β ^ 2 / 2) * algebraMap ℚ A ((V.rank E : ℤ) : ℚ) * P.cls ^ 2
        * P.cls
      = algebraMap ℚ A (β ^ 2 / 2 * ((V.rank E : ℤ) : ℚ)) * P.cls ^ 3 from by
    rw [map_mul]; ring]
  rw [show algebraMap ℚ A (-β) * V.chComp E 1 * P.cls ^ 1 * P.cls
      = algebraMap ℚ A (-β) * (V.chComp E 1 * P.cls ^ 2) from by ring]
  rw [show V.chComp E 2 * P.cls ^ 0 * P.cls = V.chComp E 2 * P.cls from by ring]
  rw [NumericalRingData.degree_algebraMap_mul, NumericalRingData.degree_algebraMap_mul]
  ring

/-- `∫ch₃^β = ∫ch₃ − β·∫H·ch₂ + (β²/2)·∫H²ch₁ − (β³/6)·∫H³ch₀`. -/
theorem deg3Beta_eq (β : ℚ) (E : N) :
    deg3Beta V P β E =
      V.ring.degree (V.chComp E 3)
        - β * V.ring.degree (V.chComp E 2 * P.cls)
        + β ^ 2 / 2 * V.ring.degree (V.chComp E 1 * P.cls ^ 2)
        - β ^ 3 / 6 * (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ)) := by
  rw [deg3Beta, chBetaComp_eq, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Nat.sub_self, Nat.sub_zero, show (3 : ℕ) - 1 = 2 from rfl,
    show (3 : ℕ) - 2 = 1 from rfl, tc0, tc1, tc2, tc3, V.chComp_zero, map_one, one_mul]
  rw [map_add, map_add, map_add]
  rw [show algebraMap ℚ A (-(β ^ 3) / 6) * algebraMap ℚ A ((V.rank E : ℤ) : ℚ) * P.cls ^ 3
      = algebraMap ℚ A (-(β ^ 3) / 6 * ((V.rank E : ℤ) : ℚ)) * P.cls ^ 3 from by
    rw [map_mul]]
  rw [show algebraMap ℚ A (β ^ 2 / 2) * V.chComp E 1 * P.cls ^ 2
      = algebraMap ℚ A (β ^ 2 / 2) * (V.chComp E 1 * P.cls ^ 2) from by ring]
  rw [show algebraMap ℚ A (-β) * V.chComp E 2 * P.cls ^ 1
      = algebraMap ℚ A (-β) * (V.chComp E 2 * P.cls) from by ring]
  rw [show V.chComp E 3 * P.cls ^ 0 = V.chComp E 3 from by ring]
  rw [NumericalRingData.degree_algebraMap_mul, NumericalRingData.degree_algebraMap_mul,
    NumericalRingData.degree_algebraMap_mul]
  ring

/-! ### The transport -/

/-- **A polarised threefold class as a point of the `(α, β)` charge plane.**

The first slot carries `∫H³`; see the module docstring. -/
noncomputable def toNumClass (E : N) : Wall.Threefold.NumClass :=
  (((V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ) : ℚ) : ℝ),
    ((V.ring.degree (V.chComp E 1 * P.cls ^ 2) : ℚ) : ℝ),
    ((V.ring.degree (V.chComp E 2 * P.cls) : ℚ) : ℝ),
    ((V.ring.degree (V.chComp E 3) : ℚ) : ℝ))

@[simp] theorem toNumClass_deg0 (E : N) :
    (toNumClass V P E).deg0 = ((V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ) : ℚ) : ℝ) := rfl

@[simp] theorem toNumClass_deg1 (E : N) :
    (toNumClass V P E).deg1 = ((V.ring.degree (V.chComp E 1 * P.cls ^ 2) : ℚ) : ℝ) := rfl

@[simp] theorem toNumClass_deg2 (E : N) :
    (toNumClass V P E).deg2 = ((V.ring.degree (V.chComp E 2 * P.cls) : ℚ) : ℝ) := rfl

@[simp] theorem toNumClass_deg3 (E : N) :
    (toNumClass V P E).deg3 = ((V.ring.degree (V.chComp E 3) : ℚ) : ℝ) := rfl

/-- The transport is additive, because rank and the three degrees all are. -/
theorem toNumClass_add (E F : N) :
    toNumClass V P (E + F) = toNumClass V P E + toNumClass V P F := by
  have h1 : V.chComp (E + F) 1 = V.chComp E 1 + V.chComp F 1 := V.chComp_add E F 1
  have h2 : V.chComp (E + F) 2 = V.chComp E 2 + V.chComp F 2 := V.chComp_add E F 2
  have h3 : V.chComp (E + F) 3 = V.chComp E 3 + V.chComp F 3 := V.chComp_add E F 3
  simp only [toNumClass, h1, h2, h3, add_mul, map_add, Prod.mk_add_mk, Prod.mk.injEq]
  push_cast
  exact ⟨by ring, by ring, by ring, by ring⟩

/-- The transport, bundled additively. -/
noncomputable def toNumClassHom : N →+ Wall.Threefold.NumClass :=
  AddMonoidHom.mk' (toNumClass V P) (toNumClass_add V P)

@[simp] theorem toNumClassHom_apply (E : N) :
    toNumClassHom V P E = toNumClass V P E := rfl

/-- **The threefold charge family of a polarised numerical threefold**, as a
pullback of the generic `(α, β)` child. -/
noncomputable def wallChargeFamily : Wall.ChargeFamily (ℝ × ℝ) N :=
  Wall.Threefold.chargeFamily.pullback (toNumClassHom V P)

@[simp] theorem wallChargeFamily_charge (p : ℝ × ℝ) (E : N) :
    (wallChargeFamily V P).charge p E =
      Wall.Threefold.charge p.1 p.2 (toNumClass V P E) := rfl

/-! ### The compressed twist is the ring twist -/

/-- **The identity the bridge turns on.**  The four-coordinate `betaTwist`
agrees with the twisted degrees `BMT.lean` reads off `chBetaComp`. -/
theorem betaTwist_toNumClass (β : ℚ) (E : N) :
    Wall.Threefold.betaTwist (β : ℝ) (toNumClass V P E) =
      (((V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ) : ℚ) : ℝ),
        ((degH1Beta V P β E : ℚ) : ℝ),
        ((degH2Beta V P β E : ℚ) : ℝ),
        ((deg3Beta V P β E : ℚ) : ℝ)) := by
  rw [degH1Beta_eq, degH2Beta_eq, deg3Beta_eq]
  simp only [Wall.Threefold.betaTwist, toNumClass_deg0, toNumClass_deg1,
    toNumClass_deg2, toNumClass_deg3, Prod.mk.injEq]
  push_cast
  exact ⟨trivial, by ring, by ring, by ring⟩

/-- The compressed discriminant is the `H`-twisted discriminant of `BMT.lean`. -/
theorem discr_betaTwist_toNumClass (β : ℚ) (E : N) :
    Wall.Threefold.discr (Wall.Threefold.betaTwist (β : ℝ) (toNumClass V P E)) =
      ((discrHBeta V P β E : ℚ) : ℝ) := by
  rw [betaTwist_toNumClass, discrHBeta]
  simp only [Wall.Threefold.discr, Wall.Threefold.NumClass.deg0,
    Wall.Threefold.NumClass.deg1, Wall.Threefold.NumClass.deg2]
  push_cast
  ring

/-- **The compressed Bayer--Macrì--Toda quantity is the one `BMT.lean`
defines.**  There is one `Q` in the library, not two. -/
theorem Q_toNumClass (α β : ℚ) (E : N) :
    Wall.Threefold.Q (α : ℝ) (β : ℝ) (toNumClass V P E) = ((Q V P α β E : ℚ) : ℝ) := by
  rw [Wall.Threefold.Q, discr_betaTwist_toNumClass, betaTwist_toNumClass,
    Threefold.Q, discrHBeta]
  simp only [Wall.Threefold.NumClass.deg1, Wall.Threefold.NumClass.deg2,
    Wall.Threefold.NumClass.deg3]
  push_cast
  ring

/-- The compressed tilt slope is the one `BMT.lean` defines. -/
theorem nu_toNumClass (α β : ℚ) (E : N) :
    Wall.Threefold.nu (α : ℝ) (β : ℝ) (toNumClass V P E) = ((nu V P α β E : ℚ) : ℝ) := by
  rw [Wall.Threefold.nu, betaTwist_toNumClass, Threefold.nu]
  simp only [Wall.Threefold.NumClass.deg1, Wall.Threefold.NumClass.deg2,
    toNumClass_deg0]
  push_cast
  ring

/-! ### The conjecture, transported and no more true than before -/

/-- **The Bayer--Macrì--Toda inequality on the transported class.**

`BMTData` is supplied data and is **false for some threefolds** — see
`BMT.lean`.  This restates it; it proves nothing about sheaves. -/
theorem Q_toNumClass_nonneg (B : BMTData V P) {α β : ℚ} {E : N} (hα : 0 < α)
    (hE : B.TiltSemistable α β E) :
    0 ≤ Wall.Threefold.Q (α : ℝ) (β : ℝ) (toNumClass V P E) := by
  rw [Q_toNumClass]
  exact_mod_cast B.nonneg α β E hα hE

end Threefold

end AlgebraicGeometry.Numerical
