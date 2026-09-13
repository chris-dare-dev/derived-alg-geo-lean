/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.VectorClass
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.ThreefoldWallTransport
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.WallTransport
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Exp

/-!
# The polarised wall transport, for every dimension and correction class

`Walls/Exp/` states the exponential charge once. This is the geometric side:
the map that turns a numerical class on a polarised variety into the compressed
`H`-degrees that the charge consumes, written once for every dimension `n`,
truncation degree `m` and correction class `κ`.

Before this the transport existed twice: `Surface.toNumClass`
(`WallTransport.lean`) at `n = 2` and `Threefold.toNumClass`
(`ThreefoldWallTransport.lean`) at `n = 3`, the second a hand-copy of the first
at one more codimension. Both are proved below to be this map.

## The rank slot carries `∫Hⁿ`

Slot `k` is `∫ H^(n-k) · (ch(E)·κ)_k`, so the index is codimension and slot `0`
is `∫Hⁿ · rk(E)`, not the bare rank. Both existing transports already did this
and said so in their docstrings, but nothing tied the convention to a root;
`hDegrees_zero` now does, in every dimension at once.

The weight is as easy to get wrong in the other direction. The slope `μ_H` is
**not** the ratio of slots `d₁/d₀`: that ratio is the slope divided by `∫Hⁿ`.
`slopeH_eq_degree_mul_ratio` states the true relation, and
`slopeH_ne_ratio_of_degree_ne_one` records the false one as a negative result,
because the naive reading was written down during this lane's own design review
and is wrong on every polarization of degree other than one.

## `κ` is a pullback, never a coefficient

The correction class enters through `corrComp`, a convolution in the right-hand
slot, and nothing else here knows which class it is. Two values matter today:
`unitCorr`, giving the plain Chern character, and `sqrtToddComp`, giving the
Mukai vector. `corrComp_sqrtToddComp` is `rfl`, because
`NumericalVarietyData.mukaiComp` was already this convolution written out, so
the Mukai vector is not a second construction. The two are pullbacks of one
transport with genuinely different walls and must not be fused into one family.

## What is proved about the existing families

`surface_toNumClass_eq` and `threefold_toNumClass_eq` are the class-level
comparisons. `surface_wallChargeFamily_eq` is the family-level one, which is
the form a consumer actually needs: the existing surface wall family is this
root's family, reindexed by the surface chart.

The threefold family-level twin is deliberately absent. It needs a truncation
map that does not exist yet, which belongs to the tilt slice; inventing a
second route to it here is exactly what the tilt adjudication exists to stop.
-/

open scoped BigOperators

noncomputable section

namespace AlgebraicGeometry.Numerical.Polarised

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

universe u v
variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]

/-- The trivial correction class `κ = 1`, giving the plain Chern character. -/
def unitCorr (A : Type u) [CommRing A] : ℕ → A := fun j => if j = 0 then 1 else 0

/-- `(ch(E)·κ)_k`, the codimension-`k` component of the corrected character.

The convolution is in the right-hand slot, which keeps `κ` a parameter rather
than a coefficient baked into the transport. -/
def corrComp (V : NumericalVarietyData n A N) (κ : ℕ → A) (E : N) (k : ℕ) : A :=
  ∑ j ∈ Finset.range (k + 1), V.chComp E j * κ (k - j)

/-- With `κ = 1` the convolution is the identity. This is the one fact both
dimension comparisons need, proved once instead of per dimension. -/
theorem corrComp_unitCorr (V : NumericalVarietyData n A N) (E : N) (k : ℕ) :
    corrComp V (unitCorr A) E k = V.chComp E k := by
  classical
  rw [corrComp, Finset.sum_eq_single k]
  · simp [unitCorr]
  · intro j hj hjk
    have hj' : j < k + 1 := Finset.mem_range.mp hj
    have : k - j ≠ 0 := by omega
    simp [unitCorr, this]
  · intro h
    exact absurd (Finset.self_mem_range_succ k) h

/-- At `κ = √td` the convolution IS the Mukai component, by `rfl`. -/
theorem corrComp_sqrtToddComp (V : NumericalVarietyData n A N) (E : N) (k : ℕ) :
    corrComp V V.sqrtToddComp E k = V.mukaiComp E k := rfl

/-- The corrected character is additive, because the Chern character is. -/
theorem corrComp_add (V : NumericalVarietyData n A N) (κ : ℕ → A) (E F : N) (k : ℕ) :
    corrComp V κ (E + F) k = corrComp V κ E k + corrComp V κ F k := by
  simp only [corrComp, V.chComp_add, add_mul, Finset.sum_add_distrib]

/-- **The compressed `H`-degree vector**, `d k = ∫ H^(n-k) · (ch(E)·κ)_k` for
`k ≤ m`. One map for every `(n, m, κ)`. -/
def hDegrees (V : NumericalVarietyData n A N) (P : Polarization V.ring)
    (κ : ℕ → A) (m : ℕ) (E : N) : Exp.HDeg m :=
  fun k => ((V.ring.degree (corrComp V κ E (k : ℕ) * P.cls ^ (n - (k : ℕ))) : ℚ) : ℝ)

/-- The transport is additive. -/
theorem hDegrees_add (V : NumericalVarietyData n A N) (P : Polarization V.ring)
    (κ : ℕ → A) (m : ℕ) (E F : N) :
    hDegrees V P κ m (E + F) = hDegrees V P κ m E + hDegrees V P κ m F := by
  funext k
  simp only [hDegrees, corrComp_add, add_mul, map_add, Pi.add_apply]
  push_cast
  ring

/-- The transport bundled as an additive map, which is what `pullback` needs. -/
def hDegreesHom (V : NumericalVarietyData n A N) (P : Polarization V.ring)
    (κ : ℕ → A) (m : ℕ) : N →+ Exp.HDeg m :=
  AddMonoidHom.mk' (hDegrees V P κ m) (by intro E F; exact hDegrees_add V P κ m E F)

/-- **The wall family of a polarised variety**: the kernel's family pulled back
along the transport. Every dimension and every correction class gets its walls
from here rather than from a charge of its own. -/
def wallChargeFamily (V : NumericalVarietyData n A N) (P : Polarization V.ring)
    (κ : ℕ → A) (m : ℕ) : ChargeFamily ℂ N :=
  (Exp.chargeFamily m).pullback (hDegreesHom V P κ m)

/-- **PROVED.**  Slot 0 is `∫Hⁿ · rank E`. -/
theorem hDegrees_zero (V : NumericalVarietyData n A N) (P : Polarization V.ring)
    (E : N) :
    V.ring.degree (corrComp V (unitCorr A) E 0 * P.cls ^ (n - 0))
      = (V.rank E : ℚ) * V.ring.degree (P.cls ^ n) := by
  have hc : corrComp V (unitCorr A) E 0 = algebraMap ℚ A (V.rank E : ℚ) := by
    rw [corrComp_unitCorr, V.chComp_zero]
  rw [hc, Nat.sub_zero, NumericalRingData.degree_algebraMap_mul]

/-! ###########################################################################
    (1) THE n = 2 COMPARISON — `WallTransport.lean:112`.
    ########################################################################### -/

/-- **The surface transport is `(n, m, κ) = (2, 2, 1)` of the root.**
`Surface.toNumClass` (WallTransport.lean:112) is exactly the root's H-degree
vector; in particular its slot 0 weighting by `∫H²` is the `k = 0` case of
`hDegrees_zero`, not a per-dimension convention. -/
theorem surface_toNumClass_eq (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (E : N) :
    Surface.toNumClass V P E
      = (hDegrees V P (unitCorr A) 2 E 0,
         hDegrees V P (unitCorr A) 2 E 1,
         hDegrees V P (unitCorr A) 2 E 2) := by
  have h0 : hDegrees V P (unitCorr A) 2 E 0
      = ((V.ring.degree (P.cls ^ 2) * (V.rank E : ℚ) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 0 * P.cls ^ (2 - 0)) : ℚ) : ℝ) = _
    rw [hDegrees_zero V P E, mul_comm]
  have h1 : hDegrees V P (unitCorr A) 2 E 1 = ((degH V P E : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 1 * P.cls ^ (2 - 1)) : ℚ) : ℝ) = _
    rw [corrComp_unitCorr]
    rfl
  have h2 : hDegrees V P (unitCorr A) 2 E 2
      = ((V.ring.degree (V.chComp E 2) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 2 * P.cls ^ (2 - 2)) : ℚ) : ℝ) = _
    rw [corrComp_unitCorr]
    norm_num
  rw [h0, h1, h2]
  rfl

/-! ###########################################################################
    (2) THE n = 3 TWIN — `ThreefoldWallTransport.lean:146`.
    The critic's finding: this was a code comment, never a declaration.
    ########################################################################### -/

/-- **The threefold transport is `(n, m, κ) = (3, 3, 1)` of the root.**
`Threefold.toNumClass` (ThreefoldWallTransport.lean:146) is the root's H-degree
vector at `n = 3`: slot 0 is `∫H³ · rank E` by `hDegrees_zero`, and slots 1–3
are `∫ H^(3-k) · ch_k(E)`. -/
theorem threefold_toNumClass_eq (V : NumericalVarietyData 3 A N)
    (P : Polarization V.ring) (E : N) :
    Threefold.toNumClass V P E
      = (hDegrees V P (unitCorr A) 3 E 0,
         hDegrees V P (unitCorr A) 3 E 1,
         hDegrees V P (unitCorr A) 3 E 2,
         hDegrees V P (unitCorr A) 3 E 3) := by
  have h0 : hDegrees V P (unitCorr A) 3 E 0
      = ((V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 0 * P.cls ^ (3 - 0)) : ℚ) : ℝ) = _
    rw [hDegrees_zero V P E, mul_comm]
  have h1 : hDegrees V P (unitCorr A) 3 E 1
      = ((V.ring.degree (V.chComp E 1 * P.cls ^ 2) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 1 * P.cls ^ (3 - 1)) : ℚ) : ℝ) = _
    rw [corrComp_unitCorr]
  have h2 : hDegrees V P (unitCorr A) 3 E 2
      = ((V.ring.degree (V.chComp E 2 * P.cls) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 2 * P.cls ^ (3 - 2)) : ℚ) : ℝ) = _
    rw [corrComp_unitCorr]
    norm_num
  have h3 : hDegrees V P (unitCorr A) 3 E 3
      = ((V.ring.degree (V.chComp E 3) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 3 * P.cls ^ (3 - 3)) : ℚ) : ℝ) = _
    rw [corrComp_unitCorr]
    norm_num
  rw [h0, h1, h2, h3]
  rfl

/-! ###########################################################################
    (3) N4 — the honest relation between `slopeH` and the root's slots.
    `slopeH` (Slope.lean:133) is `degH / rank`, while slot 0 is `rank · ∫Hⁿ`.
    So the ratio `d₁ / d₀` is NOT the slope: it is the slope divided by `∫Hⁿ`.
    ########################################################################### -/

/-- Slot 1 of the root is `degH`, in every dimension `n ≥ 1`. -/
theorem hDegrees_one (V : NumericalVarietyData n A N) (P : Polarization V.ring)
    (hn : 1 ≤ n) (E : N) :
    hDegrees V P (unitCorr A) n E ⟨1, by omega⟩ = ((degH V P E : ℚ) : ℝ) := by
  show ((V.ring.degree (corrComp V (unitCorr A) E 1 * P.cls ^ (n - 1)) : ℚ) : ℝ) = _
  rw [corrComp_unitCorr]
  rfl

/-- Pure field algebra: dividing both slots of a ratio by the same nonzero
weight scales the ratio.  Stated separately so the `rank E = 0` junk case is
visible rather than hidden inside `field_simp`. -/
private theorem ratio_aux (d D r : ℝ) (hD : D ≠ 0) : d / r = D * (d / (r * D)) := by
  rcases eq_or_ne r 0 with h | h
  · simp [h]
  · field_simp

/-- **N4, corrected and proved.**  `μ_H(E) = ∫Hⁿ · (d₁ / d₀)`.

The report's §2.6 reading `slopeH = d₁ / d₀` is FALSE whenever `∫Hⁿ ≠ 1`: the
rank slot carries the `∫Hⁿ` weight, so the ratio of the root's slots is the
slope *scaled down* by `∫Hⁿ`.  Note there is no rank hypothesis — at `rank E = 0`
both sides are Lean's junk `0`, which is the same junk `slopeH` already has. -/
theorem slopeH_eq_degree_mul_ratio (V : NumericalVarietyData n A N)
    (P : Polarization V.ring) (hn : 1 ≤ n) (E : N) :
    ((slopeH V P E : ℚ) : ℝ)
      = ((V.ring.degree (P.cls ^ n) : ℚ) : ℝ)
          * (hDegrees V P (unitCorr A) n E ⟨1, by omega⟩
              / hDegrees V P (unitCorr A) n E ⟨0, by omega⟩) := by
  have hD : (0 : ℝ) < ((V.ring.degree (P.cls ^ n) : ℚ) : ℝ) := by
    exact_mod_cast P.degree_pow_pos
  have h1 := hDegrees_one V P hn E
  have h0 : hDegrees V P (unitCorr A) n E ⟨0, by omega⟩
      = ((V.rank E : ℚ) : ℝ) * ((V.ring.degree (P.cls ^ n) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 0 * P.cls ^ (n - 0)) : ℚ) : ℝ) = _
    rw [hDegrees_zero V P E]
    push_cast
    ring
  rw [h0, h1, slopeH, Rat.cast_div]
  exact ratio_aux _ _ _ (ne_of_gt hD)

/-- **The falsified reading, recorded as a negative result.**  `slopeH = d₁/d₀`
holds exactly when `∫Hⁿ = 1` (or the slope is zero); it is not an identity. -/
theorem slopeH_ne_ratio_of_degree_ne_one (V : NumericalVarietyData n A N)
    (P : Polarization V.ring) (hn : 1 ≤ n) (E : N)
    (hdeg : V.ring.degree (P.cls ^ n) ≠ 1) (hne : slopeH V P E ≠ 0) :
    ((slopeH V P E : ℚ) : ℝ)
      ≠ hDegrees V P (unitCorr A) n E ⟨1, by omega⟩
          / hDegrees V P (unitCorr A) n E ⟨0, by omega⟩ := by
  intro h
  have hD : (0 : ℝ) < ((V.ring.degree (P.cls ^ n) : ℚ) : ℝ) := by
    exact_mod_cast P.degree_pow_pos
  have key := slopeH_eq_degree_mul_ratio V P hn E
  rw [← h] at key
  have hs : ((slopeH V P E : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast hne
  have hcancel : ((V.ring.degree (P.cls ^ n) : ℚ) : ℝ) * ((slopeH V P E : ℚ) : ℝ)
      = 1 * ((slopeH V P E : ℚ) : ℝ) := by
    rw [one_mul]
    exact key.symm
  have hone : ((V.ring.degree (P.cls ^ n) : ℚ) : ℝ) = 1 := mul_right_cancel₀ hs hcancel
  exact hdeg (by exact_mod_cast hone)


/-! ### The family-level comparison -/

/-- The surface transport's H-degree vector IS the surface lane's coordinate
identification of `Surface.toNumClass`. -/
theorem surfaceVec_toNumClass (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (E : N) :
    surfaceVec (Surface.toNumClass V P E) = hDegrees V P (unitCorr A) 2 E := by
  funext k
  rw [surface_toNumClass_eq V P E]
  fin_cases k <;> simp [surfaceVec]

/-- **The existing surface wall family is the root's, reindexed by the chart.**
This is the family-level statement; the class-level one is
`surface_toNumClass_eq`. -/
theorem surface_wallChargeFamily_eq (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) :
    Surface.wallChargeFamily V P
      = (wallChargeFamily V P (unitCorr A) 2).reindex Exp.stChart := by
  apply ChargeFamily.ext
  intro p
  ext E
  rw [Surface.wallChargeFamily_charge, stCharge_eq_exp]
  show _ = Exp.charge 2 (Exp.stChart p) (hDegrees V P (unitCorr A) 2 E)
  rw [← surfaceVec_toNumClass V P E]
  rfl

end AlgebraicGeometry.Numerical.Polarised

#print axioms AlgebraicGeometry.Numerical.Polarised.surface_wallChargeFamily_eq
