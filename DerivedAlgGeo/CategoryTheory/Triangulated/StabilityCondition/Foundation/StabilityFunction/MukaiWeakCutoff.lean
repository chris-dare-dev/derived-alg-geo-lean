/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.ExpCharge
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.WeakCutoffSlope
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.WeakSlopeCutoff

/-!
# `Z(β,ω)` read against the weak slope cutoff

`ExpCharge.lean` carries a Mukai class map into an abelian category and makes
`Z(β,ω)` a charge on objects.  It stops there, deliberately: its own docstring
records that `MukaiChargeData` asserts nothing about rank, slope or torsion, and
that bundling those as hypotheses would make the positivity a case split over
invented assumptions.

This file supplies the missing connection in the one form that is an
*identification* rather than a discriminant: `MukaiWeakSlopeCompat` says the
Mukai class's rank component **is** the rank, and its `ω`-degree **is** the
degree, of a `WeakSlopeData` on the same category.  Both are true on a polarised
surface by definition of the Mukai vector, neither mentions torsion or a cutoff,
and everything else below is proved.

## The identity everything rests on

`Mukai.im_expCharge` gives `Im Z(β,ω)(r, c, s) = ω·c - r·(β·ω)`.  Under the
identification that is

```
Im Z(β,ω)(E) = degree E - rank E · (β·ω)
```

so the **sign of `Im Z(β,ω)` is exactly the comparison of `μ(E) = degree/rank`
against the cutoff `β·ω`**.  That is the Mukai compatibility: `Z(β,ω)`'s
imaginary part and the weak slope cutoff of `WeakCutoff.lean` are two readings
of one inequality.

## Why this needs the weak theory and not the strict one

At rank zero the comparison `degree/rank` is meaningless and the identity reads
`Im Z = degree`, which `degree_nonneg_of_rank_zero` makes nonnegative and which
**vanishes exactly on the skyscraper**.  So `Im Z ≥ 0` is the sharp conclusion
for the torsion class, not `Im Z > 0`: the boundary is attained, and
`rank_eq_zero_of_im_eq_zero_of_mem_hnTors` below says it is attained only there.

That is precisely why `Z(β,ω)` before tilting is a *weak* stability function and
`WeakSlope.lean` had to exist. A strict `StabilityFunction` would have to exclude
the skyscraper, and on a K3 the skyscrapers are the subject.

## What this is not

It is still not Lemma 6.2. This file relates `Im Z(β,ω)` to the cutoff classes of
the **untilted** heart; Lemma 6.2 is the statement that `Z(β,ω)` is a stability
function on the **tilted** heart `𝒜(β,ω)`, which additionally needs `hnTilt` and
the real-part analysis of `ChargePositivity.lean` for the boundary case. The four
cases remain open, and nothing here calls them closed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

namespace WeakSlopeData

/-- **The torsion-free class at a finite cutoff contains no rank-zero object.**

The dual of `mem_hnTors_of_rank_zero`, and forced by the same fact: a rank-zero
object has slope `⊤`, which is not below any finite cutoff.  So membership in
`hnFree` at a finite cutoff already implies positive rank, and no separate rank
hypothesis is needed downstream. -/
theorem rank_pos_of_mem_hnFree (S : WeakSlopeData A)
    (hHN : S.toWeakStabilityFunction.HasHNProperty) {μ₀ : ℝ} {E : A}
    (hE : ¬IsZero E)
    (h : E ∈ WeakStabilityFunctionOn.hnFree S.toWeakStabilityFunction
      ((μ₀ : ℝ) : WithTop ℝ)) :
    0 < S.rank E := by
  have hslope := WeakStabilityFunctionOn.slope_le_of_mem_hnFree hHN hE h
  refine S.topSlope_ne_top_iff_rank_pos.mp fun htop => ?_
  rw [show S.toWeakStabilityFunction.slope E = S.topSlope E from rfl, htop] at hslope
  exact absurd (top_le_iff.mp hslope) WithTop.coe_ne_top

end WeakSlopeData

/-- **The Mukai class map computes the rank and the `ω`-degree.**

Two identifications, no discriminants: nothing here mentions torsion, a cutoff,
or the Mukai square. On a polarised surface both hold by the definition of the
Mukai vector `v(E) = (r(E), c₁(E), ch₂(E) + r(E))` together with `degree = ω·c₁`.

Compare `SlopeData`'s geometric fields, which are of the same kind. What is
deliberately *not* here is any hypothesis of the shape "E is torsion" or
"`μ(E) > β·ω`" — those are the conclusions. -/
structure MukaiWeakSlopeCompat (D : MukaiChargeData A V) (S : WeakSlopeData A)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (ω : V) where
  /-- The rank component of the Mukai class is the rank. -/
  rank_eq : ∀ E : A, (D.mukai (K₀Ab.of E)).1 = (S.rank E : ℝ)
  /-- The `ω`-degree of the Mukai class's `c₁` component is the degree. -/
  degree_eq : ∀ E : A, b ω (D.mukai (K₀Ab.of E)).2.1 = (S.degree E : ℝ)

namespace MukaiWeakSlopeCompat

variable {D : MukaiChargeData A V} {S : WeakSlopeData A}
variable {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {ω : V}
variable (C : MukaiWeakSlopeCompat D S b ω) (hb : ∀ x y : V, b x y = b y x) (β : V)

include C hb

/-- **The identity.** `Mukai.im_expCharge` under the identification: the
imaginary part of `Z(β,ω)` is the degree, shifted by the rank times the
cutoff. -/
theorem im_charge (E : A) :
    (D.charge b β ω E).im = (S.degree E : ℝ) - (S.rank E : ℝ) * b β ω := by
  rw [MukaiChargeData.charge_apply,
    Mukai.im_expCharge b β ω hb (D.mukai (K₀Ab.of E)).1
      (D.mukai (K₀Ab.of E)).2.1 (D.mukai (K₀Ab.of E)).2.2,
    C.degree_eq E, C.rank_eq E]

/-- At positive rank the sign of `Im Z(β,ω)` is the slope comparison, exactly. -/
theorem im_charge_pos_iff_of_rank_pos {E : A} (hE : 0 < S.rank E) :
    0 < (D.charge b β ω E).im ↔ ((b β ω : ℝ) : WithTop ℝ) < S.topSlope E := by
  have hr : (0 : ℝ) < (S.rank E : ℝ) := by exact_mod_cast hE
  rw [C.im_charge hb β E, S.topSlope_of_rank_pos hE, WithTop.coe_lt_coe,
    WeakSlopeData.slope, lt_div_iff₀ hr]
  constructor <;> intro h <;> nlinarith

/-- At rank zero the identity reads `Im Z = degree`, which is nonnegative for a
nonzero object — and zero exactly for the skyscraper. -/
theorem im_charge_eq_degree_of_rank_zero {E : A} (h : S.rank E = 0) :
    (D.charge b β ω E).im = (S.degree E : ℝ) := by
  rw [C.im_charge hb β E, h]
  push_cast
  ring

/-- **The torsion class has nonnegative `Im Z(β,ω)`.**

Cases 1--3 of Lemma 6.2 conclude this, and the bound is sharp rather than strict:
at rank zero `Im Z` is the degree, which vanishes on the skyscraper. -/
theorem im_charge_nonneg_of_mem_hnTors
    (hHN : S.toWeakStabilityFunction.HasHNProperty) {E : A} (hE : ¬IsZero E)
    (h : E ∈ WeakStabilityFunctionOn.hnTors S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ)) :
    0 ≤ (D.charge b β ω E).im := by
  have hslope := WeakStabilityFunctionOn.lt_slope_of_mem_hnTors hHN hE h
  rcases lt_or_eq_of_le (S.rank_nonneg E) with hpos | hzero
  · exact le_of_lt ((C.im_charge_pos_iff_of_rank_pos hb β hpos).mpr hslope)
  · rw [C.im_charge_eq_degree_of_rank_zero hb β hzero.symm]
    exact_mod_cast S.degree_nonneg_of_rank_zero E hE hzero.symm

/-- **At positive rank the bound is strict**, which is what cases 1--3 of
Lemma 6.2 need: the charge lands in the *open* upper half plane. -/
theorem im_charge_pos_of_mem_hnTors_of_rank_pos
    (hHN : S.toWeakStabilityFunction.HasHNProperty) {E : A} (hE : ¬IsZero E)
    (hrank : 0 < S.rank E)
    (h : E ∈ WeakStabilityFunctionOn.hnTors S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ)) :
    0 < (D.charge b β ω E).im :=
  (C.im_charge_pos_iff_of_rank_pos hb β hrank).mpr
    (WeakStabilityFunctionOn.lt_slope_of_mem_hnTors hHN hE h)

/-- **The boundary of the torsion class is exactly the skyscraper.**

An object of the torsion class with `Im Z(β,ω) = 0` has rank zero and degree
zero, so its μ-slope charge is `0`. This is the case that has no phase, the case
`SlopeData` cannot express, and the reason `Z(β,ω)` is only a weak stability
function here. -/
theorem rank_eq_zero_of_im_eq_zero_of_mem_hnTors
    (hHN : S.toWeakStabilityFunction.HasHNProperty) {E : A} (hE : ¬IsZero E)
    (h : E ∈ WeakStabilityFunctionOn.hnTors S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ))
    (him : (D.charge b β ω E).im = 0) : S.rank E = 0 ∧ S.degree E = 0 := by
  rcases lt_or_eq_of_le (S.rank_nonneg E) with hpos | hzero
  · exact absurd him
      (ne_of_gt (C.im_charge_pos_of_mem_hnTors_of_rank_pos hb β hHN hE hpos h))
  · refine ⟨hzero.symm, ?_⟩
    rw [C.im_charge_eq_degree_of_rank_zero hb β hzero.symm] at him
    exact_mod_cast him

/-- The sign statement for the torsion-free class. -/
theorem im_charge_nonpos_of_mem_hnFree
    (hHN : S.toWeakStabilityFunction.HasHNProperty) {E : A} (hE : ¬IsZero E)
    (h : E ∈ WeakStabilityFunctionOn.hnFree S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ)) :
    (D.charge b β ω E).im ≤ 0 := by
  have hrank := S.rank_pos_of_mem_hnFree hHN hE h
  have hslope := WeakStabilityFunctionOn.slope_le_of_mem_hnFree hHN hE h
  rw [show S.toWeakStabilityFunction.slope E = S.topSlope E from rfl,
    S.topSlope_of_rank_pos hrank, WithTop.coe_le_coe] at hslope
  have hr : (0 : ℝ) < (S.rank E : ℝ) := by exact_mod_cast hrank
  rw [WeakSlopeData.slope, div_le_iff₀ hr] at hslope
  rw [C.im_charge hb β E]
  nlinarith

end MukaiWeakSlopeCompat

end CategoryTheory.Triangulated
