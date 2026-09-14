/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.RealFormSignature
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.WallFiniteness

/-!
# `P⁺` does not depend on which class in the positive cone names it

`Orientation.lean` defines the two halves against a **fixed** reference pair, and
says plainly that reference-independence is a further statement — the
projection-sign cocycle, whose usual proof runs through connectedness of the
Grassmannian of positive planes.

This file proves the case route (A) actually needs, and proves it by a path
rather than by the cocycle: **if `ω` and `ω'` lie in the same component of the
positive cone, the exponential pairs at `ω` and at `ω'` are similarly
oriented.** So the half named by `exp(β + iω)` is the half named by
`exp(β' + iω')`, and `P⁺` is well defined by the cone rather than by a choice
inside it.

## Why a path works here and not in general

The segment from `ω` to `ω'` stays in the positive cone — that is one line of
bilinear algebra once `0 < b ω ω'` says the two are in the *same* component —
so the whole family `exp(β_t + iω_t)` consists of positive pairs, and the
pairing determinant against the reference is a continuous function of `t` that
never vanishes (`pairingDet_ne_zero`). It is positive at `t = 0`, so the
intermediate value theorem makes it positive at `t = 1`.

The general cocycle has no such path handed to it: three arbitrary positive
planes are not joined by a distinguished family. That statement remains open as
its own issue, and nothing here should be read as settling it.

## Scope

`β` is carried along the path and is otherwise unconstrained; the positivity
condition is on `ω` alone, exactly as in `isPositivePair_exp`.
-/

open QuadraticMap Set

namespace Mukai

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- A bilinear form on a finite-dimensional real normed space is jointly
continuous. It is half the polar form of its own quadratic map. -/
theorem continuous_bilin (hb : ∀ x y : V, b x y = b y x) :
    Continuous fun p : V × V => b p.1 p.2 := by
  have h := QuadraticMap.continuous_polar (LinearMap.BilinMap.toQuadraticMap b)
  have heq : (fun p : V × V => polar (⇑(LinearMap.BilinMap.toQuadraticMap b)) p.1 p.2 / 2)
      = fun p : V × V => b p.1 p.2 := by
    funext p
    rw [LinearMap.BilinMap.polar_toQuadraticMap, hb p.2 p.1]
    ring
  rw [← heq]
  exact h.div_const 2

omit [FiniteDimensional ℝ V] in
/-- The pairing determinant of two exponential pairs, in terms of `b` alone. -/
theorem pairingDet_exp (hb : ∀ x y : V, b x y = b y x) (β ω β' ω' : V) :
    PeriodDomain.pairingDet (realForm b) (expRe b β ω) (expIm b β ω)
        (expRe b β' ω') (expIm b β' ω')
      = (b β β' - (b β' β' - b ω' ω') / 2 - (b β β - b ω ω) / 2) * b ω ω'
        - (b β ω' - b β' ω') * (b ω β' - b β ω) := by
  rw [PeriodDomain.pairingDet, polar_realForm b hb, polar_realForm b hb, polar_realForm b hb,
    polar_realForm b hb]
  simp only [realPairing, pairing, expRe, expIm]
  ring

section Path

variable (β ω β' ω' : V)

/-- The straight-line family between two exponential data. -/
noncomputable def segment (t : ℝ) : V × V := ((1 - t) • β + t • β', (1 - t) • ω + t • ω')

omit [FiniteDimensional ℝ V] in
@[simp]
theorem segment_zero : segment β ω β' ω' 0 = (β, ω) := by simp [segment]

omit [FiniteDimensional ℝ V] in
@[simp]
theorem segment_one : segment β ω β' ω' 1 = (β', ω') := by simp [segment]

omit [FiniteDimensional ℝ V] in
/-- **The positive cone is convex along the segment.** Positivity of `b ω ω'` is
what says the two classes are in the *same* component of the cone; without it the
segment can pass through zero. -/
theorem pos_segment (hb : ∀ x y : V, b x y = b y x) (hω : 0 < b ω ω) (hω' : 0 < b ω' ω')
    (hcone : 0 < b ω ω') {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < b (segment β ω β' ω' t).2 (segment β ω β' ω' t).2 := by
  obtain ⟨h0, h1⟩ := ht
  have hexp : b ((1 - t) • ω + t • ω') ((1 - t) • ω + t • ω')
      = (1 - t) * (1 - t) * b ω ω + 2 * ((1 - t) * t) * b ω ω' + t * t * b ω' ω' := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hb ω' ω]
    ring
  simp only [segment]
  rw [hexp]
  rcases eq_or_lt_of_le h0 with rfl | ht0
  · simpa using hω
  · rcases eq_or_lt_of_le h1 with rfl | ht1
    · simpa using hω'
    · have h2 : 0 < 1 - t := by linarith
      have p1 : 0 < (1 - t) * (1 - t) * b ω ω := mul_pos (mul_pos h2 h2) hω
      have hmid : 0 < 2 * ((1 - t) * t) := by
        have := mul_pos h2 ht0
        linarith
      have p2 : 0 < 2 * ((1 - t) * t) * b ω ω' := mul_pos hmid hcone
      have p3 : 0 < t * t * b ω' ω' := mul_pos (mul_pos ht0 ht0) hω'
      linarith

/-- The pairing determinant along the segment, as a function of `t`. -/
noncomputable def pathDet (t : ℝ) : ℝ :=
  PeriodDomain.pairingDet (realForm b) (expRe b β ω) (expIm b β ω)
    (expRe b (segment β ω β' ω' t).1 (segment β ω β' ω' t).2)
    (expIm b (segment β ω β' ω' t).1 (segment β ω β' ω' t).2)

theorem continuous_pathDet (hb : ∀ x y : V, b x y = b y x) :
    Continuous (pathDet b β ω β' ω') := by
  have hbc := continuous_bilin b hb
  have hseg : Continuous (segment β ω β' ω') := by
    unfold segment
    fun_prop
  have hf : Continuous fun t : ℝ => (segment β ω β' ω' t).1 := hseg.fst
  have hg : Continuous fun t : ℝ => (segment β ω β' ω' t).2 := hseg.snd
  have key : ∀ f g : ℝ → V, Continuous f → Continuous g →
      Continuous fun t => b (f t) (g t) := fun f g hf hg => hbc.comp (hf.prodMk hg)
  unfold pathDet
  simp only [pairingDet_exp b hb]
  have h1 := key _ _ (continuous_const : Continuous fun _ : ℝ => β) hf
  have h2 := key _ _ hf hf
  have h3 := key _ _ hg hg
  have h4 := key _ _ (continuous_const : Continuous fun _ : ℝ => β) hg
  have h5 := key _ _ hf hg
  have h6 := key _ _ (continuous_const : Continuous fun _ : ℝ => ω) hg
  have h7 := key _ _ (continuous_const : Continuous fun _ : ℝ => ω) hf
  exact (((h1.sub ((h2.sub h3).div_const 2)).sub continuous_const).mul h6).sub
    ((h4.sub h5).mul (h7.sub continuous_const))

omit [FiniteDimensional ℝ V] in
theorem pathDet_zero (hb : ∀ x y : V, b x y = b y x) :
    pathDet b β ω β' ω' 0 = (b ω ω) ^ 2 := by
  simp only [pathDet, segment_zero]
  exact pairingDet_exp_self b β ω hb

omit [FiniteDimensional ℝ V] in
theorem pathDet_one : pathDet b β ω β' ω' 1 =
    PeriodDomain.pairingDet (realForm b) (expRe b β ω) (expIm b β ω)
      (expRe b β' ω') (expIm b β' ω') := by
  simp only [pathDet, segment_one]

/-- **The half named by `ω` is the half named by any `ω'` in the same cone.**

The determinant along the segment is continuous and never zero, and it starts
positive, so the intermediate value theorem keeps it positive at the far end.

`hsig` is not a new assumption: route (A) supplies it from the Hodge index
signature of `V` (`hasSignatureTwo_realForm`). -/
theorem mem_periodDomainPlus_exp_of_sameCone
    (hsig : PeriodDomain.HasSignatureTwo (realForm b)) (hb : ∀ x y : V, b x y = b y x)
    (hω : 0 < b ω ω) (hω' : 0 < b ω' ω') (hcone : 0 < b ω ω') :
    (expRe b β' ω', expIm b β' ω') ∈
      PeriodDomain.periodDomainPlus (realForm b) (expRe b β ω) (expIm b β ω) := by
  have hpair : ∀ t ∈ Icc (0 : ℝ) 1, PeriodDomain.IsPositivePair (realForm b)
      (expRe b (segment β ω β' ω' t).1 (segment β ω β' ω' t).2)
      (expIm b (segment β ω β' ω' t).1 (segment β ω β' ω' t).2) := fun t ht =>
    isPositivePair_exp b _ _ hb (pos_segment b β ω β' ω' hb hω hω' hcone ht)
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, pathDet b β ω β' ω' t ≠ 0 := fun t ht =>
    PeriodDomain.pairingDet_ne_zero hsig (isPositivePair_exp b β ω hb hω) (hpair t ht)
  have h0 : 0 < pathDet b β ω β' ω' 0 := by
    rw [pathDet_zero b β ω β' ω' hb]
    positivity
  have h1 : 0 < pathDet b β ω β' ω' 1 := by
    rcases lt_trichotomy (pathDet b β ω β' ω' 1) 0 with hlt | heq | hgt
    · exfalso
      have hsub := intermediate_value_Icc' (zero_le_one (α := ℝ))
        (continuous_pathDet b β ω β' ω' hb).continuousOn
      obtain ⟨c, hc, hc0⟩ := hsub ⟨le_of_lt hlt, le_of_lt h0⟩
      exact hne c hc hc0
    · exact absurd heq (hne 1 ⟨zero_le_one, le_refl 1⟩)
    · exact hgt
  refine ⟨isPositivePair_exp b β' ω' hb hω', ?_⟩
  rwa [← pathDet_one b β ω β' ω']

/-- **The same statement resting on the Hodge index hypotheses alone.**

`hasSignatureTwo_realForm` discharges the signature hypothesis, so with
`V = NS(X) ⊗ ℝ` the inputs are: the Hodge index signature of `V`, and two classes
in the same component of its positive cone. -/
theorem mem_periodDomainPlus_exp_of_sameCone_of_sigPos (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hsigNeg : sigNeg (LinearMap.BilinMap.toQuadraticMap b) + 1 = Module.finrank ℝ V)
    (hω : 0 < b ω ω) (hω' : 0 < b ω' ω') (hcone : 0 < b ω ω') :
    (expRe b β' ω', expIm b β' ω') ∈
      PeriodDomain.periodDomainPlus (realForm b) (expRe b β ω) (expIm b β ω) :=
  mem_periodDomainPlus_exp_of_sameCone b β ω β' ω'
    (hasSignatureTwo_realForm b hb hsigPos hsigNeg) hb hω hω' hcone

end Path

end Mukai
