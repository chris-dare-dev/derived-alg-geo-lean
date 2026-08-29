/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.Subobject

/-!
# Weak slopes on an abelian category

`PhaseGeometry.lean` reads a **strict** stability function through `arg`, which
is available because `semiClosedUpperHalfPlane` excludes `0`.  A **weak**
stability function does not exclude it: a skyscraper on a surface has zero rank
and zero degree, so its charge is exactly `0` and `arg 0 = 0` carries no
information.  This file therefore reads a weak stability function through its
**slope** in `WithTop ℝ` instead, with `⊤` on the whole real boundary.

That choice is not new here.  `Weak/Basic/Definitions.lean` already stores
weak slopes in `WithTop ℝ`, and `Weak/HarderNarasimhan/Heart.lean` already
indexes weak HN filtrations by them, for exactly this reason.  What is new is
that both of those live on a **t-structure**, at `heartDatum t`, and speak
through ambient distinguished triangles.  This file states the same slope on
the **abelian** side, at `abelianDatum A`, through subobjects and cokernels,
which is the shape the abelian HN development of `Uniqueness/` consumes.

## Contents

* `chargeSlope` — the slope of a complex number: `-Re/Im` when `0 < Im`, and
  `⊤` otherwise.  The two see-saw lemmas for it,
  `chargeSlope_le_add_le_of_le` and `chargeSlope_add_lt_of_lt`, are proved on
  `closedUpperHalfPlane` and treat `⊤` explicitly.  Both need the half-plane,
  not merely `0 ≤ Im`: the boundary case `Im = 0` uses `Re ≤ 0`.
* `WeakStabilityFunctionOn.slope`, `IsSemistable` at `abelianDatum A`.
* `slope_le_of_epi` — a nonzero quotient of a weak-semistable object has slope
  at least the source's.  This is the weak counterpart of
  `StabilityFunction.phase_le_of_epi`, and its proof is *shorter*: the two
  see-saw cases split on `le_total` and neither needs an `arg` estimate.
* `hom_eq_zero_of_semistable_slope_gt` — the Hom-vanishing that the HN
  uniqueness development runs on.

## The order convention, stated once

Slopes **increase** towards `⊤`, and `⊤` is the slope of a rank-zero object.
An HN filtration therefore stores a *strictly decreasing* `μ : Fin n → WithTop ℝ`
whose first value may be `⊤`, matching `WeakAbelianHNFiltration`.  Nothing below
subtracts or adds slopes; they are only ever compared, which is why `WithTop ℝ`
suffices and why the strict development ports.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex

universe u v

namespace CategoryTheory.Triangulated

/-! ## The slope of a charge value -/

/-- The **slope** of a charge value: `-Re z / Im z` when `0 < Im z`, and `⊤`
otherwise.  On `closedUpperHalfPlane` the second branch is exactly the real
boundary, including `0`, so a zero-charge object has slope `⊤` rather than an
undefined argument. -/
def chargeSlope (z : ℂ) : WithTop ℝ :=
  if 0 < z.im then ((-z.re / z.im : ℝ) : WithTop ℝ) else ⊤

theorem chargeSlope_of_im_pos {z : ℂ} (h : 0 < z.im) :
    chargeSlope z = ((-z.re / z.im : ℝ) : WithTop ℝ) :=
  if_pos h

theorem chargeSlope_of_im_nonpos {z : ℂ} (h : ¬0 < z.im) : chargeSlope z = ⊤ :=
  if_neg h

theorem chargeSlope_ne_top_iff {z : ℂ} : chargeSlope z ≠ ⊤ ↔ 0 < z.im := by
  constructor
  · intro h
    by_contra him
    exact h (chargeSlope_of_im_nonpos him)
  · intro him
    rw [chargeSlope_of_im_pos him]
    exact WithTop.coe_ne_top

theorem chargeSlope_lt_top_iff {z : ℂ} : chargeSlope z < ⊤ ↔ 0 < z.im := by
  rw [lt_top_iff_ne_top]
  exact chargeSlope_ne_top_iff

/-- Positive imaginary part on the left of a strict slope comparison. -/
theorem im_pos_of_chargeSlope_lt {z w : ℂ} (h : chargeSlope z < chargeSlope w) :
    0 < z.im :=
  chargeSlope_lt_top_iff.mp (lt_of_lt_of_le h le_top)

/-- Membership in the closed upper half-plane bounds the imaginary part. -/
theorem im_nonneg_of_mem_closedUpperHalfPlane {z : ℂ}
    (hz : z ∈ closedUpperHalfPlane) : 0 ≤ z.im := by
  rcases hz with h | ⟨h, _⟩
  · exact h.le
  · exact h.ge

/-- The real part is nonpositive on the boundary of the closed upper
half-plane. -/
theorem re_nonpos_of_mem_closedUpperHalfPlane_of_im_eq_zero {z : ℂ}
    (hz : z ∈ closedUpperHalfPlane) (him : z.im = 0) : z.re ≤ 0 := by
  rcases hz with h | ⟨_, h⟩
  · exact absurd him h.ne'
  · exact h

/-- **The non-strict see-saw.**  If the two ends of a short exact sequence have
ordered slopes, the middle slope lies between them.  Three cases: both interior,
one on the boundary, both on the boundary.  The `⊤` branch is where the weak
theory differs from the strict one, and it is handled rather than excluded. -/
theorem chargeSlope_le_add_le_of_le {z w : ℂ} (hz : z ∈ closedUpperHalfPlane)
    (hw : w ∈ closedUpperHalfPlane) (h : chargeSlope z ≤ chargeSlope w) :
    chargeSlope z ≤ chargeSlope (z + w) ∧ chargeSlope (z + w) ≤ chargeSlope w := by
  have him : (z + w).im = z.im + w.im := by simp
  have hre : (z + w).re = z.re + w.re := by simp
  by_cases hzim : 0 < z.im
  · by_cases hwim : 0 < w.im
    · have hsum : 0 < (z + w).im := by rw [him]; positivity
      have hcross : -z.re * w.im ≤ -w.re * z.im := by
        rw [chargeSlope_of_im_pos hzim, chargeSlope_of_im_pos hwim] at h
        have h' : -z.re / z.im ≤ -w.re / w.im := by exact_mod_cast h
        exact (div_le_div_iff₀ hzim hwim).1 h'
      rw [chargeSlope_of_im_pos hzim, chargeSlope_of_im_pos hwim,
        chargeSlope_of_im_pos hsum]
      constructor
      · exact_mod_cast (div_le_div_iff₀ hzim hsum).2 (by rw [him, hre]; nlinarith)
      · exact_mod_cast (div_le_div_iff₀ hsum hwim).2 (by rw [him, hre]; nlinarith)
    · -- `w` is on the boundary: `slope w = ⊤`, and `w.re ≤ 0` pushes the sum up.
      have hwim0 : w.im = 0 := le_antisymm (not_lt.mp hwim)
        (im_nonneg_of_mem_closedUpperHalfPlane hw)
      have hwre : w.re ≤ 0 :=
        re_nonpos_of_mem_closedUpperHalfPlane_of_im_eq_zero hw hwim0
      have hsum : 0 < (z + w).im := by rw [him, hwim0, add_zero]; exact hzim
      rw [chargeSlope_of_im_pos hzim, chargeSlope_of_im_nonpos hwim,
        chargeSlope_of_im_pos hsum]
      refine ⟨?_, le_top⟩
      have : -z.re / z.im ≤ -(z + w).re / (z + w).im := by
        rw [him, hwim0, add_zero, hre]
        exact (div_le_div_iff_of_pos_right hzim).2 (by linarith)
      exact_mod_cast this
  · -- `z` is on the boundary: `slope z = ⊤`, so `slope w = ⊤` too.
    have hzim0 : z.im = 0 := le_antisymm (not_lt.mp hzim)
      (im_nonneg_of_mem_closedUpperHalfPlane hz)
    rw [chargeSlope_of_im_nonpos hzim] at h
    have hwtop : chargeSlope w = ⊤ := top_le_iff.mp h
    have hwim : ¬0 < w.im := by
      intro hpos
      rw [chargeSlope_of_im_pos hpos] at hwtop
      exact WithTop.coe_ne_top hwtop
    have hwim0 : w.im = 0 := le_antisymm (not_lt.mp hwim)
      (im_nonneg_of_mem_closedUpperHalfPlane hw)
    have hsum : ¬0 < (z + w).im := by rw [him, hzim0, hwim0]; simp
    rw [chargeSlope_of_im_nonpos hzim, chargeSlope_of_im_nonpos hsum, hwtop]
    exact ⟨le_rfl, le_rfl⟩

/-- **The strict see-saw.**  If the quotient end is strictly below the sub end,
the middle is strictly below the sub end too.  Both `⊤` cases are decided by
`im_pos_of_chargeSlope_lt`. -/
theorem chargeSlope_add_lt_of_lt {z w : ℂ} (hz : z ∈ closedUpperHalfPlane)
    (h : chargeSlope w < chargeSlope z) : chargeSlope (z + w) < chargeSlope z := by
  have him : (z + w).im = z.im + w.im := by simp
  have hre : (z + w).re = z.re + w.re := by simp
  have hwim : 0 < w.im := im_pos_of_chargeSlope_lt h
  by_cases hzim : 0 < z.im
  · have hsum : 0 < (z + w).im := by rw [him]; positivity
    have hcross : -w.re * z.im < -z.re * w.im := by
      rw [chargeSlope_of_im_pos hzim, chargeSlope_of_im_pos hwim] at h
      have h' : -w.re / w.im < -z.re / z.im := by exact_mod_cast h
      exact (div_lt_div_iff₀ hwim hzim).1 h'
    rw [chargeSlope_of_im_pos hzim, chargeSlope_of_im_pos hsum]
    exact_mod_cast (div_lt_div_iff₀ hsum hzim).2 (by rw [him, hre]; nlinarith)
  · have hzim0 : z.im = 0 := le_antisymm (not_lt.mp hzim)
      (im_nonneg_of_mem_closedUpperHalfPlane hz)
    have hsum : 0 < (z + w).im := by rw [him, hzim0, zero_add]; exact hwim
    rw [chargeSlope_of_im_nonpos hzim, chargeSlope_of_im_pos hsum]
    exact WithTop.coe_lt_top _

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace WeakStabilityFunctionOn

variable (W : WeakStabilityFunctionOn (abelianDatum A))

/-- The central charge on objects. -/
abbrev charge (E : A) : ℂ := W.Z (K₀Ab.of E)

@[simp]
theorem charge_apply (E : A) : W.charge E = W.Z (K₀Ab.of E) := rfl

/-- Nonzero objects have charge in the closed upper half-plane. -/
theorem charge_mem (E : A) (hE : ¬IsZero E) :
    W.charge E ∈ closedUpperHalfPlane :=
  W.nonzero_mem E hE

/-- **Zero objects have zero charge.** -/
theorem map_zero (E : A) (hE : IsZero E) : W.charge E = 0 := by
  rw [charge_apply, K₀Ab.of_isZero hE]
  exact W.Z.map_zero

/-- **Isomorphic objects have the same charge.** -/
theorem map_iso {E F : A} (e : E ≅ F) : W.charge E = W.charge F := by
  rw [charge_apply, charge_apply, K₀Ab.of_iso e]

/-- **The charge is additive on short exact sequences.** -/
theorem additive (S : ShortComplex A) (hS : S.ShortExact) :
    W.charge S.X₂ = W.charge S.X₁ + W.charge S.X₃ := by
  rw [charge_apply, charge_apply, charge_apply, K₀Ab.of_shortExact S hS, map_add]

/-- The **weak slope** of an object, in `WithTop ℝ`, with `⊤` exactly on the
real boundary of the closed upper half-plane — in particular at charge `0`. -/
def slope (E : A) : WithTop ℝ := chargeSlope (W.charge E)

theorem slope_eq_chargeSlope (E : A) : W.slope E = chargeSlope (W.charge E) := rfl

theorem slope_of_im_pos {E : A} (h : 0 < (W.charge E).im) :
    W.slope E = ((-(W.charge E).re / (W.charge E).im : ℝ) : WithTop ℝ) :=
  chargeSlope_of_im_pos h

theorem slope_of_im_nonpos {E : A} (h : ¬0 < (W.charge E).im) : W.slope E = ⊤ :=
  chargeSlope_of_im_nonpos h

/-- **A zero-charge object has slope `⊤`.**  This is the skyscraper, and it is
the case a phase-indexed weak cutoff cannot express. -/
theorem slope_eq_top_of_charge_eq_zero {E : A} (h : W.charge E = 0) :
    W.slope E = ⊤ :=
  chargeSlope_of_im_nonpos (by rw [h]; simp)

theorem slope_eq_of_iso {E F : A} (e : E ≅ F) : W.slope E = W.slope F := by
  rw [slope_eq_chargeSlope, slope_eq_chargeSlope, W.map_iso e]

/-- **Weak semistability**: no nonzero subobject has slope above the object's
own.  The comparison is in `WithTop ℝ`, so a rank-zero subobject of slope `⊤`
forces the ambient slope to be `⊤` as well. -/
def IsSemistable (E : A) : Prop :=
  ¬IsZero E ∧ ∀ B : Subobject E, ¬IsZero (B : A) → W.slope (B : A) ≤ W.slope E

/-- **Weak stability**: every nonzero proper subobject has strictly smaller
slope. -/
def IsStable (E : A) : Prop :=
  ¬IsZero E ∧ ∀ B : Subobject E, ¬IsZero (B : A) → B ≠ ⊤ →
    W.slope (B : A) < W.slope E

theorem IsStable.isSemistable {E : A} (h : W.IsStable E) : W.IsSemistable E := by
  refine ⟨h.1, fun B hB => ?_⟩
  by_cases htop : B = ⊤
  · subst htop
    exact le_of_eq (W.slope_eq_of_iso (asIso (⊤ : Subobject E).arrow))
  · exact (h.2 B hB htop).le

theorem isSemistable_of_iso {E F : A} (e : E ≅ F) (h : W.IsSemistable E) :
    W.IsSemistable F := by
  refine ⟨fun hF => h.1 (hF.of_iso e), fun B hB => ?_⟩
  let B' : Subobject E := Subobject.mk (B.arrow ≫ e.inv)
  have hB' : ¬IsZero (B' : A) := fun hzero =>
    hB (hzero.of_iso (Subobject.underlyingIso (B.arrow ≫ e.inv)).symm)
  have hle := h.2 B' hB'
  rw [W.slope_eq_of_iso (Subobject.underlyingIso (B.arrow ≫ e.inv))] at hle
  rwa [W.slope_eq_of_iso e] at hle

theorem isSemistable_iff_of_iso {E F : A} (e : E ≅ F) :
    W.IsSemistable E ↔ W.IsSemistable F :=
  ⟨W.isSemistable_of_iso e, W.isSemistable_of_iso e.symm⟩

/-- **A nonzero quotient of a weak-semistable object has slope at least the
source's.**

The weak counterpart of `StabilityFunction.phase_le_of_epi`, and shorter: the
kernel's slope is bounded by semistability, and the two see-saws decide the
remaining comparison by `le_total` without any `arg` estimate. -/
theorem slope_le_of_epi {E Q : A} (p : E ⟶ Q) [Epi p] (hE : W.IsSemistable E)
    (hQ : ¬IsZero Q) : W.slope E ≤ W.slope Q := by
  by_cases hker : IsZero (kernel p)
  · haveI : Mono p := Preadditive.mono_of_kernel_zero
      (zero_of_source_iso_zero _ hker.isoZero)
    haveI : IsIso p := isIso_of_mono_of_epi p
    exact le_of_eq (W.slope_eq_of_iso (asIso p))
  have hkerle : W.slope (kernel p) ≤ W.slope E := by
    calc W.slope (kernel p)
        = W.slope (kernelSubobject p : A) :=
          W.slope_eq_of_iso (kernelSubobjectIso p).symm
      _ ≤ W.slope E := hE.2 _ fun hzero =>
          hker (hzero.of_iso (kernelSubobjectIso p).symm)
  have hshort : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance
  have hsum : W.charge E = W.charge (kernel p) + W.charge Q := W.additive _ hshort
  have hkmem := W.charge_mem (kernel p) hker
  have hqmem := W.charge_mem Q hQ
  rcases le_total (W.slope (kernel p)) (W.slope Q) with hle | hle
  · -- The see-saw places `E` between the two ends.
    have := (chargeSlope_le_add_le_of_le hkmem hqmem hle).2
    rwa [← hsum] at this
  · -- Otherwise the strict see-saw contradicts semistability, unless equality.
    rcases eq_or_lt_of_le hle with heq | hlt
    · have := (chargeSlope_le_add_le_of_le hqmem hkmem (le_of_eq heq)).2
      rw [add_comm, ← hsum] at this
      exact heq ▸ this
    · exfalso
      have hstrict := chargeSlope_add_lt_of_lt hkmem hlt
      rw [← hsum] at hstrict
      exact absurd hkerle (not_le.mpr hstrict)

/-- **Hom-vanishing between weak-semistable objects of decreasing slope.**  The
image is a quotient of the source and a subobject of the target, so its slope is
trapped; a strict slope drop leaves no room for it. -/
theorem hom_eq_zero_of_semistable_slope_gt {E F : A} (hE : W.IsSemistable E)
    (hF : W.IsSemistable F) (hslope : W.slope F < W.slope E) (f : E ⟶ F) :
    f = 0 := by
  by_contra hf
  have himage : ¬IsZero (image f) := by
    intro hzero
    apply hf
    have hι : image.ι f = 0 := zero_of_source_iso_zero _ hzero.isoZero
    rw [← image.fac f, hι, comp_zero]
  have hsource := W.slope_le_of_epi (factorThruImage f) hE himage
  have htarget : W.slope (image f) ≤ W.slope F := by
    calc W.slope (image f)
        = W.slope (imageSubobject f : A) :=
          W.slope_eq_of_iso (imageSubobjectIso f).symm
      _ ≤ W.slope F := hF.2 _ fun hzero =>
          himage (hzero.of_iso (imageSubobjectIso f).symm)
  exact (not_lt_of_ge (hsource.trans htarget)) hslope

end WeakStabilityFunctionOn

end CategoryTheory.Triangulated
