/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PositiveFrameOpen

/-!
# The projection-sign cocycle

`PositiveFrame.lean` splits the positive frames in two by the sign of `pairingDet`
against a fixed reference pair, and says plainly that the split might depend on
the reference. It does not. For any three positive frames

```
0 < pairingDet r p * pairingDet p q * pairingDet q r
```

(`pairingDet_cocycle`), so the sign against one reference is the product of the
signs through any other; `sameOrientation_iff_of_reference` turns that into
independence of the partition, which is what makes `positiveFramesPlus` *the*
half rather than *a* half.

## The proof, and what it does not use

The textbook argument runs through connectedness of the Grassmannian of
positive planes. That is not used here and not assumed. What replaces it is
that a positive frame can be pushed into the reference plane along an explicit
straight line that never leaves the positive frames:

* `proj` is orthogonal projection onto the reference plane, written by Cramer's
  rule out of the reference's own Gram determinant — invertible exactly because
  the reference is positive. No orthogonal-complement theory is needed.
* `isPositiveFrame_interp`: the whole segment `t ↦ (πx + t x', πy + t y')`,
  `t ∈ [0, 1]`, consists of positive frames. The residual lies where `Q` is
  nonpositive, so shrinking it only increases `Q` on every combination.
* `pairingDet_proj`: the determinant against the reference does not move along
  that segment at all. It only ever sees the projection.
* `pairingDet_proj_mul_pos`: the determinant against a *second* reference keeps
  its sign along it.

At `t = 0` both pairs lie in the reference plane and the identity is algebra:
`pairingDet_ref_comb` turns two of the three factors into the same
change-of-basis determinant times a Gram determinant, so that determinant
appears squared and its sign drops out.

## The analytic input, named

One step is not algebra: `pairingDet_proj_mul_pos` is the intermediate value
theorem, applied through `pos_mul_endpoints_of_ne_zero` to a quadratic
polynomial in `t` that `pairingDet_ne_zero` forbids from vanishing on `[0, 1]`.
That is `intermediate_value_Icc` on `ℝ`, used once, and it is a theorem rather
than a hypothesis — the connectedness that the textbook proof assumes about the
Grassmannian is nowhere required.
-/

noncomputable section

open QuadraticMap

namespace PeriodDomain

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}

/-- The pairing determinant is symmetric in the two pairs: it is the same
`2 × 2` determinant read along the other diagonal. -/
theorem pairingDet_comm (x₀ y₀ x y : M) :
    pairingDet Q x₀ y₀ x y = pairingDet Q x y x₀ y₀ := by
  rw [pairingDet, pairingDet, polar_comm (⇑Q) x x₀, polar_comm (⇑Q) y y₀,
    polar_comm (⇑Q) x y₀, polar_comm (⇑Q) y x₀]
  ring

/-- Replacing the reference pair by a combination scales the determinant by the
determinant of the combination. -/
theorem pairingDet_ref_comb (x₀ y₀ x y : M) (a b c d : ℝ) :
    pairingDet Q (a • x₀ + b • y₀) (c • x₀ + d • y₀) x y =
      (a * d - b * c) * pairingDet Q x₀ y₀ x y := by
  simp only [pairingDet, polar_add_left, polar_smul_left, smul_eq_mul]
  ring

/-- The determinant of a pair against itself is its Gram determinant. -/
theorem pairingDet_self (x y : M) :
    pairingDet Q x y x y = 4 * Q x * Q y - polar (⇑Q) x y ^ 2 := by
  rw [pairingDet, polar_self, polar_self, polar_comm (⇑Q) y x]
  ring

/-- A positive frame has positive Gram determinant. -/
theorem pairingDet_self_pos {x y : M} (h : IsPositiveFrame Q x y) :
    0 < pairingDet Q x y x y := by
  rw [pairingDet_self]
  exact ((isPositiveFrame_iff x y).1 h).2

/-- **A pair is positive exactly when `Q` is positive on every nontrivial
combination.** Sylvester's criterion in the form the interpolation argument
wants. -/
theorem isPositiveFrame_iff_forall_combination (x y : M) :
    IsPositiveFrame Q x y ↔
      ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → 0 < Q (a • x + b • y) := by
  rw [isPositiveFrame_iff]
  constructor
  · rintro ⟨hx, hdisc⟩ a b hab
    rw [apply_smul_add_smul]
    rcases eq_or_ne b 0 with rfl | hb
    · have ha : a ≠ 0 := by tauto
      have haa : 0 < a * a := mul_self_pos.mpr ha
      nlinarith
    · have hbb : 0 < b * b := mul_self_pos.mpr hb
      nlinarith [sq_nonneg (2 * a * Q x + b * polar (⇑Q) x y)]
  · intro h
    have hx : 0 < Q x := by simpa using h 1 0 (Or.inl one_ne_zero)
    refine ⟨hx, ?_⟩
    have hcomb := h (-(polar (⇑Q) x y)) (2 * Q x) (Or.inr (by positivity))
    rw [apply_smul_add_smul] at hcomb
    nlinarith

section Projection

variable (Q)

/-- The `x₀`-coefficient of the orthogonal projection onto the reference plane,
solved out of the `2 × 2` Gram system by Cramer. -/
def projCoeffFst (x₀ y₀ v : M) : ℝ :=
  (polar (⇑Q) y₀ y₀ * polar (⇑Q) x₀ v - polar (⇑Q) x₀ y₀ * polar (⇑Q) y₀ v) /
    pairingDet Q x₀ y₀ x₀ y₀

/-- The `y₀`-coefficient of the orthogonal projection onto the reference plane. -/
def projCoeffSnd (x₀ y₀ v : M) : ℝ :=
  (polar (⇑Q) x₀ x₀ * polar (⇑Q) y₀ v - polar (⇑Q) x₀ y₀ * polar (⇑Q) x₀ v) /
    pairingDet Q x₀ y₀ x₀ y₀

/-- **Orthogonal projection onto the plane of a positive frame**, written out in
the pair's own coordinates.  No general orthogonal-complement theory is needed:
the Gram determinant of a positive frame is invertible, so Cramer's rule gives
the projection directly. -/
def proj (x₀ y₀ v : M) : M :=
  projCoeffFst Q x₀ y₀ v • x₀ + projCoeffSnd Q x₀ y₀ v • y₀

variable {Q}

theorem polar_proj_fst {x₀ y₀ : M} (h₀ : IsPositiveFrame Q x₀ y₀) (v : M) :
    polar (⇑Q) x₀ (proj Q x₀ y₀ v) = polar (⇑Q) x₀ v := by
  have hg : pairingDet Q x₀ y₀ x₀ y₀ ≠ 0 := ne_of_gt (pairingDet_self_pos h₀)
  simp only [proj, polar_add_right, polar_smul_right, smul_eq_mul, projCoeffFst,
    projCoeffSnd]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hg]
  simp only [pairingDet, polar_comm (⇑Q) y₀ x₀]
  ring

theorem polar_proj_snd {x₀ y₀ : M} (h₀ : IsPositiveFrame Q x₀ y₀) (v : M) :
    polar (⇑Q) y₀ (proj Q x₀ y₀ v) = polar (⇑Q) y₀ v := by
  have hg : pairingDet Q x₀ y₀ x₀ y₀ ≠ 0 := ne_of_gt (pairingDet_self_pos h₀)
  simp only [proj, polar_add_right, polar_smul_right, smul_eq_mul, projCoeffFst,
    projCoeffSnd]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hg]
  simp only [pairingDet, polar_comm (⇑Q) y₀ x₀]
  ring

theorem proj_mem_pairSpan (Q) (x₀ y₀ v : M) : proj Q x₀ y₀ v ∈ pairSpan x₀ y₀ := by
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_) <;>
    exact Submodule.subset_span (by simp)

/-- What the projection is for: the residual is orthogonal to the reference
plane, so `Q` is nonpositive on it. -/
theorem sub_proj_mem_orthogonal {x₀ y₀ : M} (h₀ : IsPositiveFrame Q x₀ y₀) (v : M) :
    v - proj Q x₀ y₀ v ∈ orthogonal Q (pairSpan x₀ y₀) := by
  rw [pairSpan, mem_orthogonal_span_pair_iff]
  constructor
  · rw [polar_sub_right, polar_proj_fst h₀, sub_self]
  · rw [polar_sub_right, polar_proj_snd h₀, sub_self]

/-- **The determinant only sees the projection.**  Both entries of each column
are pairings against the reference, and those are unchanged by projecting. -/
theorem pairingDet_proj {x₀ y₀ : M} (h₀ : IsPositiveFrame Q x₀ y₀) (x y : M) :
    pairingDet Q x₀ y₀ (proj Q x₀ y₀ x) (proj Q x₀ y₀ y) = pairingDet Q x₀ y₀ x y := by
  rw [pairingDet, pairingDet, polar_proj_fst h₀, polar_proj_fst h₀,
    polar_proj_snd h₀, polar_proj_snd h₀]

end Projection

section Interpolation

/-- A continuous nonvanishing function on `[0, 1]` takes the same sign at both
ends.  This is the only analytic input the cocycle needs. -/
theorem pos_mul_endpoints_of_ne_zero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0) : 0 < f 0 * f 1 := by
  have h0 : f 0 ≠ 0 := hne 0 ⟨le_rfl, zero_le_one⟩
  have h1 : f 1 ≠ 0 := hne 1 ⟨zero_le_one, le_rfl⟩
  rcases lt_trichotomy (f 0 * f 1) 0 with hlt | heq | hgt
  · exfalso
    obtain ⟨c, hc, hc0⟩ : ∃ c ∈ Set.Icc (0 : ℝ) 1, f c = 0 := by
      rcases lt_or_gt_of_ne h0 with hneg | hpos
      · have hpos1 : 0 < f 1 := by nlinarith
        obtain ⟨c, hc, hc0⟩ :=
          intermediate_value_Icc zero_le_one hf ⟨hneg.le, hpos1.le⟩
        exact ⟨c, hc, hc0⟩
      · have hneg1 : f 1 < 0 := by nlinarith
        obtain ⟨c, hc, hc0⟩ :=
          intermediate_value_Icc' zero_le_one hf ⟨hneg1.le, hpos.le⟩
        exact ⟨c, hc, hc0⟩
    exact hne c hc hc0
  · exact absurd heq (mul_ne_zero h0 h1)
  · exact hgt

variable [FiniteDimensional ℝ M]

/-- **Shrinking the orthogonal component keeps a pair positive.**  The residual
lies where `Q` is nonpositive, so scaling it down by `t ≤ 1` only increases
`Q` on every combination. -/
theorem isPositiveFrame_interp (hsig : HasSignatureTwo Q) {x₀ y₀ x y : M}
    (h₀ : IsPositiveFrame Q x₀ y₀) (h : IsPositiveFrame Q x y) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsPositiveFrame Q (proj Q x₀ y₀ x + t • (x - proj Q x₀ y₀ x))
      (proj Q x₀ y₀ y + t • (y - proj Q x₀ y₀ y)) := by
  set px := proj Q x₀ y₀ x with hpx
  set py := proj Q x₀ y₀ y with hpy
  rw [isPositiveFrame_iff_forall_combination]
  intro a b hab
  set u : M := a • px + b • py with hu
  set w : M := a • (x - px) + b • (y - py) with hw
  have hrewrite : a • (px + t • (x - px)) + b • (py + t • (y - py)) = u + t • w := by
    rw [hu, hw]; module
  have hwmem : w ∈ orthogonal Q (pairSpan x₀ y₀) :=
    Submodule.add_mem _
      (Submodule.smul_mem _ _ (sub_proj_mem_orthogonal h₀ x))
      (Submodule.smul_mem _ _ (sub_proj_mem_orthogonal h₀ y))
  have humem : u ∈ pairSpan x₀ y₀ :=
    Submodule.add_mem _
      (Submodule.smul_mem _ _ (proj_mem_pairSpan Q x₀ y₀ x))
      (Submodule.smul_mem _ _ (proj_mem_pairSpan Q x₀ y₀ y))
  have hpolar : polar (⇑Q) u w = 0 := (mem_orthogonal_iff.1 hwmem) u humem
  have hQw : Q w ≤ 0 :=
    nonpos_of_mem_orthogonal hsig (isPositivePlane_framePlane h₀) hwmem
  have hsum : Q u + Q w = Q (a • x + b • y) := by
    have huw : u + w = a • x + b • y := by rw [hu, hw]; module
    have := polar (⇑Q) u w
    have hexp : Q (u + w) = Q u + Q w + polar (⇑Q) u w := by
      rw [polar]; ring
    rw [huw, hpolar, add_zero] at hexp
    exact hexp.symm
  have hxy : 0 < Q (a • x + b • y) :=
    (isPositiveFrame_iff_forall_combination x y).1 h a b hab
  have hexp : Q (u + t • w) = Q u + t * t * Q w := by
    have h1 : Q (u + t • w) = Q u + Q (t • w) + polar (⇑Q) u (t • w) := by
      rw [polar]; ring
    rw [QuadraticMap.map_smul, polar_smul_right, hpolar] at h1
    rw [h1]; ring
  rw [hrewrite, hexp]
  have htt : t * t ≤ 1 := by nlinarith
  have hkey : Q w ≤ t * t * Q w := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t * t)
      (by linarith : (0:ℝ) ≤ -Q w)]
  linarith

/-- **The sign against a second reference survives the projection.**  The two
frames are the ends of an interpolation through positive frames, and the
determinant against `(u, v)` is a quadratic polynomial along it that never
vanishes. -/
theorem pairingDet_proj_mul_pos (hsig : HasSignatureTwo Q) {x₀ y₀ u v x y : M}
    (h₀ : IsPositiveFrame Q x₀ y₀) (huv : IsPositiveFrame Q u v)
    (h : IsPositiveFrame Q x y) :
    0 < pairingDet Q u v (proj Q x₀ y₀ x) (proj Q x₀ y₀ y) *
      pairingDet Q u v x y := by
  set px := proj Q x₀ y₀ x with hpxdef
  set py := proj Q x₀ y₀ y with hpydef
  have hpoly : (fun t : ℝ =>
        pairingDet Q u v (px + t • (x - px)) (py + t • (y - py))) =
      fun t : ℝ =>
        (polar (⇑Q) u px + t * polar (⇑Q) u (x - px)) *
            (polar (⇑Q) v py + t * polar (⇑Q) v (y - py)) -
          (polar (⇑Q) u py + t * polar (⇑Q) u (y - py)) *
            (polar (⇑Q) v px + t * polar (⇑Q) v (x - px)) := by
    funext t
    simp only [pairingDet, polar_add_right, polar_smul_right, smul_eq_mul]
  have hcont : ContinuousOn (fun t : ℝ =>
      pairingDet Q u v (px + t • (x - px)) (py + t • (y - py)))
      (Set.Icc 0 1) := by
    rw [hpoly]
    fun_prop
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      pairingDet Q u v (px + t • (x - px)) (py + t • (y - py)) ≠ 0 := by
    intro t ht
    exact pairingDet_ne_zero hsig huv
      (isPositiveFrame_interp hsig h₀ h ht.1 ht.2)
  have key := pos_mul_endpoints_of_ne_zero hcont hne
  have e0x : px + (0 : ℝ) • (x - px) = px := by module
  have e0y : py + (0 : ℝ) • (y - py) = py := by module
  have e1x : px + (1 : ℝ) • (x - px) = x := by module
  have e1y : py + (1 : ℝ) • (y - py) = y := by module
  simpa only [e0x, e0y, e1x, e1y] using key

/-- **The projection-sign cocycle.**  For any three positive frames the three
pairing determinants taken cyclically have positive product, so the sign
against one reference is the product of the signs through any other. -/
theorem pairingDet_cocycle (hsig : HasSignatureTwo Q) {x₀ y₀ u v x y : M}
    (h₀ : IsPositiveFrame Q x₀ y₀) (huv : IsPositiveFrame Q u v)
    (h : IsPositiveFrame Q x y) :
    0 < pairingDet Q x₀ y₀ x y * pairingDet Q x y u v *
      pairingDet Q u v x₀ y₀ := by
  set px := proj Q x₀ y₀ x with hpxdef
  set py := proj Q x₀ y₀ y with hpydef
  set a₁ := projCoeffFst Q x₀ y₀ x with ha₁
  set b₁ := projCoeffSnd Q x₀ y₀ x with hb₁
  set a₂ := projCoeffFst Q x₀ y₀ y with ha₂
  set b₂ := projCoeffSnd Q x₀ y₀ y with hb₂
  have hpx : px = a₁ • x₀ + b₁ • y₀ := rfl
  have hpy : py = a₂ • x₀ + b₂ • y₀ := rfl
  have hg : 0 < pairingDet Q x₀ y₀ x₀ y₀ := pairingDet_self_pos h₀
  have hA : pairingDet Q x₀ y₀ x y =
      (a₁ * b₂ - b₁ * a₂) * pairingDet Q x₀ y₀ x₀ y₀ := by
    rw [← pairingDet_proj h₀ x y, ← hpxdef, ← hpydef, pairingDet_comm, hpx, hpy,
      pairingDet_ref_comb]
  have hB : pairingDet Q u v px py =
      (a₁ * b₂ - b₁ * a₂) * pairingDet Q u v x₀ y₀ := by
    rw [pairingDet_comm, hpx, hpy, pairingDet_ref_comb,
      pairingDet_comm x₀ y₀ u v]
  have hIVT := pairingDet_proj_mul_pos hsig h₀ huv h
  rw [← hpxdef, ← hpydef] at hIVT
  have hrewrite : pairingDet Q x₀ y₀ x y * pairingDet Q x y u v *
      pairingDet Q u v x₀ y₀ =
      pairingDet Q x₀ y₀ x₀ y₀ *
        (pairingDet Q u v px py * pairingDet Q u v x y) := by
    rw [hA, hB, pairingDet_comm x y u v]
    ring
  rw [hrewrite]
  exact mul_pos hg hIVT

/-- **The orientation partition does not depend on the reference.**  Changing
the reference pair either preserves every sign or flips every sign, so
`SameOrientation` against one positive frame is `SameOrientation` against any
other. -/
theorem sameOrientation_iff_of_reference (hsig : HasSignatureTwo Q)
    {x₀ y₀ u v : M} (h₀ : IsPositiveFrame Q x₀ y₀) (huv : IsPositiveFrame Q u v)
    {p q : M × M} (hp : IsPositiveFrame Q p.1 p.2)
    (hq : IsPositiveFrame Q q.1 q.2) :
    SameOrientation Q x₀ y₀ p q ↔ SameOrientation Q u v p q := by
  set sp := pairingDet Q x₀ y₀ p.1 p.2 with hsp
  set sq := pairingDet Q x₀ y₀ q.1 q.2 with hsq
  set tp := pairingDet Q u v p.1 p.2 with htp
  set tq := pairingDet Q u v q.1 q.2 with htq
  set c := pairingDet Q u v x₀ y₀ with hcdef
  have hcp : 0 < sp * tp * c := by
    have := pairingDet_cocycle hsig h₀ huv hp
    rwa [pairingDet_comm p.1 p.2 u v] at this
  have hcq : 0 < sq * tq * c := by
    have := pairingDet_cocycle hsig h₀ huv hq
    rwa [pairingDet_comm q.1 q.2 u v] at this
  have hc2 : 0 < c * c := mul_self_pos.mpr (pairingDet_ne_zero hsig huv h₀)
  have hprod : 0 < sp * sq * (tp * tq) := by
    have h1 : 0 < sp * tp * c * (sq * tq * c) := mul_pos hcp hcq
    rcases le_or_gt (sp * sq * (tp * tq)) 0 with hle | hlt
    · exact absurd h1 (by nlinarith [mul_nonneg (neg_nonneg.2 hle) hc2.le])
    · exact hlt
  rw [SameOrientation, SameOrientation, ← hsp, ← hsq, ← htp, ← htq]
  constructor
  · intro hpq
    rcases le_or_gt (tp * tq) 0 with hle | hlt
    · exact absurd hprod (by nlinarith [mul_nonneg hpq.le (neg_nonneg.2 hle)])
    · exact hlt
  · intro hpq
    rcases le_or_gt (sp * sq) 0 with hle | hlt
    · exact absurd hprod (by nlinarith [mul_nonneg (neg_nonneg.2 hle) hpq.le])
    · exact hlt

end Interpolation

end PeriodDomain
