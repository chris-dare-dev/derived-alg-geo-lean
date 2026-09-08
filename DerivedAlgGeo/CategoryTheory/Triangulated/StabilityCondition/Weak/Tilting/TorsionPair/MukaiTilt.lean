/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.WeakHnTilt
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.MukaiWeakCutoff
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.ExpChargeCases
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.HeartComparison

/-!
# `Z(β,ω)` on the tilted heart: the imaginary half

`MukaiWeakCutoff.lean` (#808) reads the sign of `Im Z(β,ω)` against the cutoff classes of the
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
new assumption to discharge — which is the failure mode `ExpCharge.lean` warns about and that the
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
imaginary half, and even the closed half-plane needs `Re ≤ 0` on the boundary, which is not here.

The boundary is where the remaining work is, and it is blocked for reasons outside this lane:

* the non-spherical and spherical cases (`Mukai.re_expCharge_pos_of_nonneg`,
  `re_expCharge_pos_of_neg_one`) both take the Mukai square as a **hypothesis**, and supplying it
  for a `μ`-stable sheaf is the paper's Lemma 5.1 — Serre duality, Riemann--Roch, finite
  dimensional `Hom` — which is not in this repository (#332);
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

variable (t : TStructure C)

/-- **The heart datum of an ambient Mukai class map**, by restriction along `K₀Ab.toAmbient`.

This is the whole content of the "ambient charge" problem: take the charge on `K₀ C` as
primitive and restrict, rather than take the heart charge as primitive and postulate a lift. -/
def ofAmbient (m : K₀ C →+ Mukai.RealExtension V) :
    MukaiChargeData t.heart.FullSubcategory V where
  mukai := m.comp (K₀Ab.toAmbient t)

@[simp]
theorem ofAmbient_mukai (m : K₀ C →+ Mukai.RealExtension V)
    (E : t.heart.FullSubcategory) :
    (ofAmbient t m).mukai (K₀Ab.of E) = m (K₀.of C E.obj) := by
  simp [ofAmbient]

/-- The ambient charge, on any object of `C`. -/
def ambientCharge (m : K₀ C →+ Mukai.RealExtension V)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V) (X : C) : ℂ :=
  Mukai.expCharge b β ω (m (K₀.of C X))

/-- On a heart object the ambient charge is the restricted heart charge — by construction. -/
@[simp]
theorem ambientCharge_obj (m : K₀ C →+ Mukai.RealExtension V)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V) (E : t.heart.FullSubcategory) :
    ambientCharge m b β ω E.obj = (ofAmbient t m).charge b β ω E := by
  rw [ambientCharge, MukaiChargeData.charge_apply, ofAmbient_mukai]

omit [IsTriangulated C] in
/-- The ambient charge is additive on distinguished triangles. -/
theorem ambientCharge_triangle (m : K₀ C →+ Mukai.RealExtension V)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V) {T : Triangle C} (hT : T ∈ distTriang C) :
    ambientCharge m b β ω T.obj₂ =
      ambientCharge m b β ω T.obj₁ + ambientCharge m b β ω T.obj₃ := by
  rw [ambientCharge, ambientCharge, ambientCharge, K₀.of_triangle C T hT, map_add,
    expCharge_add]

omit [IsTriangulated C] in
/-- A shift negates the ambient charge. -/
theorem ambientCharge_shift (m : K₀ C →+ Mukai.RealExtension V)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V) (X : C) :
    ambientCharge m b β ω (X⟦(1 : ℤ)⟧) = -ambientCharge m b β ω X := by
  rw [ambientCharge, ambientCharge, K₀.of_shift_one, map_neg, expCharge_neg]

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
  rw [ambientCharge, ← expCharge_neg]
  simpa [v] using hcase

end MukaiWeakSlopeCompat

end CategoryTheory.Triangulated
