/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.WeakHnTilt
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Mukai.Slope
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Mukai.NumericalCases
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Mukai.Ambient

/-!
# The Mukai exponential charge on an HN-tilted heart

`Mukai.Slope` reads the sign of `Im Z(β,ω)` against the cutoff classes of the
**untilted** heart.  `WeakHnTilt.lean` builds the tilt.  This file joins them: **every object of
the tilted heart has `0 ≤ Im Z(β,ω)`.**

## The obstruction this removes

`MukaiChargeData` carries `mukai : K₀Ab A →+ Mukai.RealExtension V` — a charge on an *abelian*
category.  The tilted heart's objects are *ambient*: `hnTilt_heart_iff` presents `X : C` inside a
triangle `F₀⟦1⟧ → X → T₀`, and only `F₀` and `T₀` lie in `t.heart`.  So nothing could be said
about `Z(X)` at all: the additivity was available, the charge was not.

**The fix is a restriction, not a hypothesis.**  Take the charge on `K₀ C` as the primitive and
*define* the heart datum by composing with `K₀Ab.toAmbient` (`GrothendieckGroup/HeartComparison.lean`).
Compatibility is then `rfl` rather than a field, so there is no new structure to inhabit and no
new assumption to discharge — which is the failure mode `Mukai.Charge` warns about and that the
`single-instantiation` gate now catches.

Note this uses only the **map** `K₀Ab 𝒜 →+ K₀ C`.  The *isomorphism* `K(𝒜) ≅ K(D)` is
unavailable at this pin and is not assumed; `HeartComparison.lean` says so, and nothing here needs
it.

## The argument

`K₀.of_triangle` and `K₀.of_shift_one` give `Z(X) = -Z(F₀) + Z(T₀)`.  #808 bounds the two ends —
`Im Z(T₀) ≥ 0` because `T₀` is torsion, `Im Z(F₀) ≤ 0` because `F₀` is torsion-free — and the
signs combine.  The zero object is handled separately at each end, where the charge vanishes.

## What this is still not

It is **not** Bridgeland's Lemma 6.2.  Lemma 6.2 needs the charge in
`semiClosedUpperHalfPlane` — `Im > 0`, or `Im = 0` **and `Re < 0`**.  This supplies only the
imaginary half for arbitrary tilted-heart objects.  The adapters below close the
strict-below, positive-rank torsion, dimension-zero, and boundary-generator cases
when their numerical hypotheses are supplied explicitly.

The remaining geometric and torsion work is outside this lane:

* the non-spherical and spherical cases (`Mukai.re_expCharge_pos_of_nonneg`,
  `re_expCharge_pos_of_neg_one`) both take the Mukai square as a **hypothesis**.  The
  assembly-safe boundary adapter takes that bound factorwise; supplying it for
  each `μ`-stable factor is the paper's Lemma 5.1 — Serre duality,
  Riemann--Roch, finite-dimensional `Hom` — which is not in this repository
  (#332);
* the torsion cases split by **dimension of support** and use ampleness, and `WeakSlopeData`
  carries a rank and a degree and nothing else.

Neither is a case analysis, and nothing here pretends otherwise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe u v

namespace CategoryTheory.Triangulated

attribute [local instance] TStructure.heartFullSubcategoryAbelian

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

namespace MukaiChargeData

variable {t : TStructure C}

/-- **The zero-dimensional torsion numerical shadow.**

If a heart object has Mukai class `(0, 0, s)` with `0 < s`, its ambient
charge lies on the negative real ray.  The class equation is an explicit
support-dimension input; this theorem does not assert that an arbitrary
rank-zero object has that class. -/
theorem mem_semiClosedUpperHalfPlane_of_ambientCharge_of_dimension_zero
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    {T₀ : t.heart.FullSubcategory} {s : ℝ}
    (hclass : (ofAmbient t m).mukai (K₀Ab.of T₀) = ((0 : ℝ), (0 : V), s))
    (hs : 0 < s) :
    ambientCharge m b β ω T₀.obj ∈ semiClosedUpperHalfPlane := by
  rw [ambientCharge_obj, charge_apply, hclass]
  exact mem_semiClosedUpperHalfPlane_of_dimension_zero b β ω hb hs

end MukaiChargeData

namespace MukaiWeakSlopeCompat

open MukaiChargeData WeakStabilityFunctionOn

variable {t : TStructure C}

/-- **Every object of the tilted heart has `0 ≤ Im Z(β,ω)`.**

The imaginary half of Bridgeland's Lemma 6.2, on the tilted heart.  The triangle
`F₀⟦1⟧ → X → T₀` of `hnTilt_heart_iff` splits the charge; #808 signs the two ends; the shift
flips the torsion-free one so both contributions are nonnegative.

This is **not** Lemma 6.2: that needs `Re < 0` on the `Im = 0` boundary, which is blocked on
Lemma 5.1 and on dimension-of-support data.  See the module docstring. -/
theorem im_ambientCharge_nonneg_of_mem_hnTilt_heart
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    {X : C}
    (hX : (S.toWeakStabilityFunction.hnTilt ((b β ω : ℝ) : WithTop ℝ) hHN).heart X) :
    0 ≤ (ambientCharge m b β ω X).im := by
  obtain ⟨F₀, T₀, hF, hT, f, g, h, hdist⟩ :=
    (S.toWeakStabilityFunction.hnTilt_heart_iff _ hHN X).mp hX
  -- The triangle splits the charge, with the shift negating the torsion-free end.
  have hsplit : ambientCharge m b β ω X =
      -ambientCharge m b β ω F₀ + ambientCharge m b β ω T₀ := by
    have := ambientCharge_triangle m b β ω hdist
    simpa [ambientCharge_shift] using this
  -- The torsion end is nonnegative.
  obtain ⟨hTheart, hTors⟩ := hT
  have hT0 : 0 ≤ (ambientCharge m b β ω T₀).im := by
    by_cases hz : IsZero (⟨T₀, hTheart⟩ : t.heart.FullSubcategory)
    · rw [show T₀ = (⟨T₀, hTheart⟩ : t.heart.FullSubcategory).obj from rfl,
        ambientCharge_obj,
        MukaiChargeData.charge_zero b β ω (ofAmbient t m) hz]
      simp
    · rw [show T₀ = (⟨T₀, hTheart⟩ : t.heart.FullSubcategory).obj from rfl,
        ambientCharge_obj]
      exact Cpt.im_charge_nonneg_of_mem_hnTors hb β hHN hz hTors
  -- The torsion-free end is nonpositive, so its negation is nonnegative.
  obtain ⟨hFheart, hFree⟩ := hF
  have hF0 : (ambientCharge m b β ω F₀).im ≤ 0 := by
    by_cases hz : IsZero (⟨F₀, hFheart⟩ : t.heart.FullSubcategory)
    · rw [show F₀ = (⟨F₀, hFheart⟩ : t.heart.FullSubcategory).obj from rfl,
        ambientCharge_obj,
        MukaiChargeData.charge_zero b β ω (ofAmbient t m) hz]
      simp
    · rw [show F₀ = (⟨F₀, hFheart⟩ : t.heart.FullSubcategory).obj from rfl,
        ambientCharge_obj]
      exact Cpt.im_charge_nonpos_of_mem_hnFree hb β hHN hz hFree
  rw [hsplit]
  simp only [Complex.add_im, Complex.neg_im]
  linarith

/-- **The strict-below free-generator case of the upper-half-plane argument.**

If `F₀` is a nonzero object of the weak HN torsion-free class at the cutoff and its
slope is strictly below `b β ω`, then the shifted object `F₀⟦1⟧` has ambient charge in
`semiClosedUpperHalfPlane`.  The proof exposes the paper's sign convention: the
charge of `F₀` has negative imaginary part, and the shift negates it.

This closes only the strict-below generator case (case 3), not the full Lemma 6.2
theorem.  The boundary equality case and the rank-zero torsion/point cases still
need the geometric Mukai-square and support-dimension inputs described in the module
docstring.  `MukaiWeakSlopeCompat` contributes only the rank/degree compatibility;
no K3 or Bogomolov--Gieseker statement is assumed here. -/
theorem mem_semiClosedUpperHalfPlane_of_shift_hnFree_of_slope_lt
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    {F₀ : t.heart.FullSubcategory} (hF₀ : ¬IsZero F₀)
    (hF : F₀ ∈ WeakStabilityFunctionOn.hnFree S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ))
    (hbelow : S.slope F₀ < b β ω) :
    ambientCharge m b β ω (F₀.obj⟦(1 : ℤ)⟧) ∈ semiClosedUpperHalfPlane := by
  have hrank : 0 < S.rank F₀ := S.rank_pos_of_mem_hnFree hHN hF₀ hF
  have him : (ofAmbient t m).charge b β ω F₀ =
      Mukai.expCharge b β ω ((ofAmbient t m).mukai (K₀Ab.of F₀)) := rfl
  have him_neg : ((ofAmbient t m).charge b β ω F₀).im < 0 := by
    rw [Cpt.im_charge hb β F₀]
    rw [WeakSlopeData.slope] at hbelow
    have hr : (0 : ℝ) < (S.rank F₀ : ℝ) := by exact_mod_cast hrank
    have hbelow' : (S.degree F₀ : ℝ) < b β ω * (S.rank F₀ : ℝ) := by
      rw [div_lt_iff₀ hr] at hbelow
      exact hbelow
    exact sub_neg.mpr (by simpa [mul_comm] using hbelow')
  let v : Mukai.RealExtension V := (ofAmbient t m).mukai (K₀Ab.of F₀)
  have hbelow' : b ω (v.2.1 - v.1 • β) < 0 := by
    rw [← Mukai.im_expCharge_eq_apply_sub_smul b β ω hb]
    change (Mukai.expCharge b β ω v).im < 0
    rw [← him]
    exact him_neg
  have hcase := neg_mem_semiClosedUpperHalfPlane_of_apply_sub_smul_neg
    (b := b) (β := β) (ω := ω) (r := v.1) (c := v.2.1) (s := v.2.2) hb hbelow'
  rw [ambientCharge_shift]
  rw [ambientCharge, ambientChargeHom_apply, ← expCharge_neg]
  simpa [v] using hcase

/-- **The positive-rank HN-torsion generator case.**

An object of the weak HN torsion class with positive rank has strictly positive
imaginary charge by `MukaiWeakSlopeCompat`.  This is the open-upper-half-plane
part of the untilted torsion generator; rank-zero torsion is intentionally left
for a separate support-dimension input. -/
theorem mem_semiClosedUpperHalfPlane_of_hnTors_of_rank_pos
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    {T₀ : t.heart.FullSubcategory} (hT₀ : ¬IsZero T₀)
    (hrank : 0 < S.rank T₀)
    (hT : T₀ ∈ WeakStabilityFunctionOn.hnTors S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ)) :
    ambientCharge m b β ω T₀.obj ∈ semiClosedUpperHalfPlane := by
  rw [ambientCharge_obj]
  exact mem_semiClosedUpperHalfPlane_of_im_pos
    (Cpt.im_charge_pos_of_mem_hnTors_of_rank_pos hb β hHN hT₀ hrank hT)

section Boundary

variable [FiniteDimensional ℝ V]

/-- **The boundary free-generator case, assembled from factorwise bounds.**

`G` is the nonempty family of boundary factors whose Mukai classes sum to the
class of `F₀`.  Positive rank and equality with the cutoff force every factor's
imaginary charge to vanish; the Mukai-square hypothesis is imposed separately
on every factor.  The numerical factorwise theorem then adds their positive
real charges before applying the shift.

This is the API intended for final Lemma 6.2 assembly.  A geometric consumer
should instantiate `G` with stable factors and prove `hGsquare` from the K3
stable-sheaf bound. -/
theorem mem_semiClosedUpperHalfPlane_of_shift_of_boundary_factors
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 2 < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    {F₀ : t.heart.FullSubcategory} {n : ℕ} (hn : 0 < n)
    (G : Fin n → t.heart.FullSubcategory)
    (hclass : (ofAmbient t m).mukai (K₀Ab.of F₀) =
      ∑ i, (ofAmbient t m).mukai (K₀Ab.of (G i)))
    (hGrank : ∀ i, 0 < S.rank (G i))
    (hGslope : ∀ i, S.slope (G i) = b β ω)
    (hGsquare : ∀ i, -1 ≤ Mukai.realForm b
      ((ofAmbient t m).mukai (K₀Ab.of (G i)))) :
    ambientCharge m b β ω (F₀.obj⟦(1 : ℤ)⟧) ∈ semiClosedUpperHalfPlane := by
  classical
  let v : Fin n → Mukai.RealExtension V := fun i ↦
    (ofAmbient t m).mukai (K₀Ab.of (G i))
  have hr : ∀ i, (1 : ℝ) ≤ (v i).1 := by
    intro i
    have hpos := hGrank i
    have hri : (1 : ℤ) ≤ S.rank (G i) := by omega
    have hri' : (1 : ℝ) ≤ (S.rank (G i) : ℝ) := by exact_mod_cast hri
    change (1 : ℝ) ≤ ((ofAmbient t m).mukai (K₀Ab.of (G i))).1
    rw [Cpt.rank_eq]
    exact hri'
  have him : ∀ i, (Mukai.expCharge b β ω (v i)).im = 0 := by
    intro i
    change ((ofAmbient t m).charge b β ω (G i)).im = 0
    exact Cpt.im_charge_eq_zero_of_rank_pos_of_slope_eq hb β (hGrank i) (hGslope i)
  have hv : ∀ i, -1 ≤ Mukai.realForm b (v i) := by
    intro i
    simpa [v] using hGsquare i
  have hcase := neg_sum_mem_semiClosedUpperHalfPlane_of_boundary_of_neg_one
    (b := b) (β := β) (ω := ω) hb hsigPos hω hn v hr him hv
  have hclass' : m (K₀.of C F₀.obj) = ∑ i, v i := by
    rw [← ofAmbient_mukai t m F₀, hclass]
  rw [ambientCharge_shift, ambientCharge, ambientChargeHom_apply, hclass', ← expCharge_neg]
  exact hcase

/-- **Low-level one-class boundary adapter with an explicit Mukai-square input.**

If the weak HN torsion-free generator lies exactly on the cutoff, the imaginary
part vanishes.  The supplied bound `-1 ≤ Mukai.realForm` is the halved Mukai
square bound for the boundary sheaf; together with `ω² > 2`, the existing
numerical positivity theorem puts the shifted charge on the allowed negative
real ray.

The Mukai-square bound is intentionally a theorem input rather than a field of
`MukaiChargeData`.  This theorem is useful when a bound on the whole class is
already available, but it is **not** the final assembly seam: `-1 ≤ v²` is not
preserved by extensions.  Use
`mem_semiClosedUpperHalfPlane_of_shift_of_boundary_factors` when the bound is
known only for stable factors. -/
theorem mem_semiClosedUpperHalfPlane_of_shift_hnFree_of_slope_eq_of_mukai_square_ge_neg_one
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 2 < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    {F₀ : t.heart.FullSubcategory} (hF₀ : ¬IsZero F₀)
    (hF : F₀ ∈ WeakStabilityFunctionOn.hnFree S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ))
    (heq : S.slope F₀ = b β ω)
    (hMukaiSquare : -1 ≤ Mukai.realForm b
      ((ofAmbient t m).mukai (K₀Ab.of F₀))) :
    ambientCharge m b β ω (F₀.obj⟦(1 : ℤ)⟧) ∈ semiClosedUpperHalfPlane := by
  have hrank : 0 < S.rank F₀ := S.rank_pos_of_mem_hnFree hHN hF₀ hF
  refine mem_semiClosedUpperHalfPlane_of_shift_of_boundary_factors
    (t := t) (n := 1) hb hsigPos hω Cpt Nat.one_pos (fun _ ↦ F₀) ?_ ?_ ?_ ?_
  · simp
  · intro
    exact hrank
  · intro
    exact heq
  · intro
    exact hMukaiSquare

end Boundary

end MukaiWeakSlopeCompat

end CategoryTheory.Triangulated
