/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PositivePlane

/-!
# Positive frames, their underlying planes, and the sign that models `P⁺`

Bridgeland's period domain is not `P` but one connected component of it, `P⁺` —
the one containing `exp(iω)` for an ample class. A component is picked out by an
**orientation** of the positive plane, and `PeriodDomain.positivePlanes` is a set of
submodules, which carries none: `Re Ω` and `Im Ω` are an ordered pair and the
plane forgets the order.

This file keeps the order. A positive frame is an ordered pair spanning a positive
plane. The map `framePlane` forgets its ordered basis, and
`forgetPositiveFrame` is the corresponding map between the two locus subtypes.
The invariant separating the two oriented halves is the sign of a `2 × 2`
determinant of pairings against a reference frame.

## Why the determinant cannot vanish, and where that comes from

For positive planes `W` and `W₀`, orthogonal projection `W → W₀` is an
isomorphism: its kernel is `W ∩ W₀ᗮ`, and a nonzero vector there would have
`Q v > 0` because it lies in `W` and `Q v < 0` because `W₀ᗮ` is negative
definite. That is `neg_of_mem_orthogonal`, and `pairingDet_ne_zero` is exactly
this argument written in coordinates, which avoids projections and determinants
of linear maps entirely.

## "Component" is modeled here, not proved

Two things are **not** claimed, and a definition that quietly assumed either
would be wrong:

* **That there are exactly two connected components.** That needs connectedness
  of the Grassmannian of positive planes — topology, not lattice theory. What is
proved is that the sign invariant splits the positive frames into two nonempty
  disjoint halves; whether each half is connected is not addressed.
* **That the positive half is Bridgeland's.** Selecting the component containing
  `exp(iω) = (1, iω, -ω²/2)` needs the Mukai extension's own vectors and an ample
  class, so it needs the bridge from `Mukai.MukaiLattice` to a bundled form that
  is out of scope here as it was in the period-domain file. Relative to a
  reference frame, "positive half" means only what its definition says.

Reference-independence of the *partition* — that changing the reference either
preserves every sign or flips every sign — is not proved *here*, but it is
proved: it is the cocycle of `QuadraticForm/PositiveFrameOrientation.lean`, which
imports this file.
-/

open QuadraticMap

namespace PeriodDomain

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}

section Defs

variable (Q)

/-- Forget the ordered basis of a frame and retain only the plane it spans. -/
def framePlane (p : M × M) : Submodule ℝ M := pairSpan p.1 p.2

/-- An **ordered positive frame**: an ordered pair spanning a positive plane. -/
def IsPositiveFrame (x y : M) : Prop := IsPositivePlane Q (framePlane (x, y))

/-- The locus of ordered positive frames. It is not the positive-plane locus:
different ordered bases can have the same image under `framePlane`. -/
def positiveFrames : Set (M × M) := {p | IsPositiveFrame Q p.1 p.2}

/-- The `2 × 2` determinant of pairings of `(x, y)` against a reference pair
`(x₀, y₀)`. Up to the positive factor `det` of the reference Gram matrix this is
the determinant of the orthogonal projection onto the reference plane, which is
why its sign is an orientation. -/
def pairingDet (x₀ y₀ x y : M) : ℝ :=
  polar (⇑Q) x₀ x * polar (⇑Q) y₀ y - polar (⇑Q) x₀ y * polar (⇑Q) y₀ x

end Defs

/-- A positive frame forgets to a positive plane. -/
theorem isPositivePlane_framePlane {p : M × M} (h : p ∈ positiveFrames Q) :
    framePlane p ∈ positivePlanes Q := h

/-- The explicit forgetful map from ordered positive frames to unoriented
positive planes. No inverse is chosen: a plane has many ordered bases. -/
def forgetPositiveFrame (p : positiveFrames Q) : positivePlanes Q :=
  ⟨framePlane p, isPositivePlane_framePlane p.property⟩

@[simp]
theorem forgetPositiveFrame_coe (p : positiveFrames Q) :
    ((forgetPositiveFrame p : positivePlanes Q) : Submodule ℝ M) = framePlane p := rfl

/-- A nontrivial combination of a positive frame is nonzero: the frame spans a
plane, so it is independent. -/
theorem combination_ne_zero {x y : M} (h : IsPositiveFrame Q x y) {a b : ℝ}
    (hab : a ≠ 0 ∨ b ≠ 0) : a • x + b • y ≠ 0 := by
  intro hzero
  -- the plane is two-dimensional, so a dependence collapses it to a line
  have hrank : Module.finrank ℝ (pairSpan x y) = 2 := h.finrank_eq
  rcases hab with ha | hb
  · have hx : x = (-(b / a)) • y := by
      have : a • x = (-b) • y := by
        rw [neg_smul]
        linear_combination (norm := module) hzero
      calc x = a⁻¹ • (a • x) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
        _ = a⁻¹ • ((-b) • y) := by rw [this]
        _ = (-(b / a)) • y := by rw [smul_smul]; ring_nf
    have hsub : pairSpan x y ≤ Submodule.span ℝ ({y} : Set M) := by
      rw [pairSpan, Submodule.span_le]
      rintro z (rfl | rfl)
      · exact hx ▸ Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · exact Submodule.subset_span rfl
    have hle1 : Module.finrank ℝ (pairSpan x y) ≤ 1 := by
      refine le_trans (Submodule.finrank_mono hsub) ?_
      rcases eq_or_ne y 0 with rfl | hy
      · rw [Submodule.span_zero_singleton]
        simp
      · exact le_of_eq (finrank_span_singleton hy)
    omega
  · have hy : y = (-(a / b)) • x := by
      have : b • y = (-a) • x := by
        rw [neg_smul]
        linear_combination (norm := module) hzero
      calc y = b⁻¹ • (b • y) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = b⁻¹ • ((-a) • x) := by rw [this]
        _ = (-(a / b)) • x := by rw [smul_smul]; ring_nf
    have hsub : pairSpan x y ≤ Submodule.span ℝ ({x} : Set M) := by
      rw [pairSpan, Submodule.span_le]
      rintro z (rfl | rfl)
      · exact Submodule.subset_span rfl
      · exact hy ▸ Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have hle1 : Module.finrank ℝ (pairSpan x y) ≤ 1 := by
      refine le_trans (Submodule.finrank_mono hsub) ?_
      rcases eq_or_ne x 0 with rfl | hx
      · rw [Submodule.span_zero_singleton]
        simp
      · exact le_of_eq (finrank_span_singleton hx)
    omega

section FiniteDimensional

variable [FiniteDimensional ℝ M]

/-- **The pairing determinant against a positive reference pair never vanishes.**

A vanishing determinant produces a nonzero vector of the plane orthogonal to both
reference vectors, hence in the reference plane's orthogonal complement, where
`Q` is negative definite — while it lies in a plane where `Q` is positive
definite. This is `neg_of_mem_orthogonal` in coordinates. -/
theorem pairingDet_ne_zero (hsig : HasSignatureTwo Q) {x₀ y₀ x y : M}
    (h₀ : IsPositiveFrame Q x₀ y₀) (h : IsPositiveFrame Q x y) :
    pairingDet Q x₀ y₀ x y ≠ 0 := by
  intro hdet
  rw [pairingDet] at hdet
  set A := polar (⇑Q) x₀ x with hA
  set B := polar (⇑Q) x₀ y with hB
  set C := polar (⇑Q) y₀ x with hC
  set D := polar (⇑Q) y₀ y with hD
  -- a nontrivial combination of `x` and `y` killed by both reference pairings
  obtain ⟨a, b, hab, ha, hc⟩ :
      ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a * A + b * B = 0 ∧ a * C + b * D = 0 := by
    rcases eq_or_ne A 0 with hA0 | hA0
    · rcases eq_or_ne B 0 with hB0 | hB0
      · rcases eq_or_ne C 0 with hC0 | hC0
        · rcases eq_or_ne D 0 with hD0 | hD0
          · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hA0, hB0], by simp [hC0, hD0]⟩
          · exact ⟨-D, C, Or.inl (neg_ne_zero.mpr hD0), by simp [hA0, hB0], by rw [hC0]; ring⟩
        · exact ⟨-D, C, Or.inr hC0, by simp [hA0, hB0], by ring⟩
      · exact ⟨-B, A, Or.inl (neg_ne_zero.mpr hB0), by ring, by linarith [hdet]⟩
    · exact ⟨-B, A, Or.inr hA0, by ring, by linarith [hdet]⟩
  set v := a • x + b • y with hv
  have hv0 : v ≠ 0 := combination_ne_zero h hab
  have hmemW : v ∈ pairSpan x y := by
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  have hperp : v ∈ orthogonal Q (pairSpan x₀ y₀) := by
    rw [pairSpan, mem_orthogonal_span_pair_iff]
    constructor
    · rw [hv, polar_add_right, polar_smul_right, polar_smul_right, smul_eq_mul, smul_eq_mul]
      linarith [ha]
    · rw [hv, polar_add_right, polar_smul_right, polar_smul_right, smul_eq_mul, smul_eq_mul]
      linarith [hc]
  have hpos : 0 < Q v := by
    have hvFrame : (⟨v, hmemW⟩ : framePlane (x, y)) ≠ 0 := by
      intro hvz
      exact hv0 (congrArg Subtype.val hvz)
    have := h.posDef ⟨v, hmemW⟩ hvFrame
    rwa [restrict_apply] at this
  have hneg : Q v < 0 := neg_of_mem_orthogonal hsig h₀ hperp hv0
  linarith

/-- Two positive frames are **similarly oriented** when their determinants against
the reference agree in sign.

The relation is stated against a fixed reference on purpose. That changing the
reference either preserves every sign or flips every one — so that the
*partition* is reference-free — is a genuine further statement: it is the cocycle
identity for the projection signs. It is proved downstream, in
`QuadraticForm/PositiveFrameOrientation.lean`, as `sameOrientation_iff_of_reference`;
the proof there interpolates through positive frames rather than importing
connectedness of the Grassmannian. -/
def SameOrientation (Q : QuadraticForm ℝ M) (x₀ y₀ : M) (p q : M × M) : Prop :=
  0 < pairingDet Q x₀ y₀ p.1 p.2 * pairingDet Q x₀ y₀ q.1 q.2

theorem sameOrientation_refl (hsig : HasSignatureTwo Q) {x₀ y₀ : M}
    (h₀ : IsPositiveFrame Q x₀ y₀) {p : M × M} (hp : IsPositiveFrame Q p.1 p.2) :
    SameOrientation Q x₀ y₀ p p :=
  mul_self_pos.mpr (pairingDet_ne_zero hsig h₀ hp)

omit [FiniteDimensional ℝ M] in
theorem sameOrientation_symm {x₀ y₀ : M} {p q : M × M}
    (h : SameOrientation Q x₀ y₀ p q) : SameOrientation Q x₀ y₀ q p := by
  rw [SameOrientation, mul_comm]
  exact h

theorem sameOrientation_trans (hsig : HasSignatureTwo Q) {x₀ y₀ : M}
    (h₀ : IsPositiveFrame Q x₀ y₀) {p q r : M × M} (hq : IsPositiveFrame Q q.1 q.2)
    (hpq : SameOrientation Q x₀ y₀ p q) (hqr : SameOrientation Q x₀ y₀ q r) :
    SameOrientation Q x₀ y₀ p r := by
  have hq0 := pairingDet_ne_zero hsig h₀ hq
  have hq2 : 0 < pairingDet Q x₀ y₀ q.1 q.2 * pairingDet Q x₀ y₀ q.1 q.2 :=
    mul_self_pos.mpr hq0
  rw [SameOrientation] at hpq hqr ⊢
  nlinarith [hpq, hqr, hq2]

end FiniteDimensional

/-- Swapping the pair flips the sign: this is what makes the invariant an
orientation rather than an arbitrary label. -/
theorem pairingDet_swap (x₀ y₀ x y : M) :
    pairingDet Q x₀ y₀ y x = -pairingDet Q x₀ y₀ x y := by
  rw [pairingDet, pairingDet]
  ring

/-- Swapping the reference pair flips the sign too. -/
theorem pairingDet_swap_ref (x₀ y₀ x y : M) :
    pairingDet Q y₀ x₀ x y = -pairingDet Q x₀ y₀ x y := by
  rw [pairingDet, pairingDet]
  ring

section Halves

variable (Q) [FiniteDimensional ℝ M]

/-- The **positive half** relative to a reference pair: `P⁺` as far as this file
can honestly define it. -/
def positiveFramesPlus (x₀ y₀ : M) : Set (M × M) :=
  {p | IsPositiveFrame Q p.1 p.2 ∧ 0 < pairingDet Q x₀ y₀ p.1 p.2}

/-- The other half. -/
def positiveFramesMinus (x₀ y₀ : M) : Set (M × M) :=
  {p | IsPositiveFrame Q p.1 p.2 ∧ pairingDet Q x₀ y₀ p.1 p.2 < 0}

variable {Q}

omit [FiniteDimensional ℝ M] in
theorem disjoint_positiveFramesPlus_minus (x₀ y₀ : M) :
    Disjoint (positiveFramesPlus Q x₀ y₀) (positiveFramesMinus Q x₀ y₀) := by
  rw [Set.disjoint_left]
  rintro p ⟨-, hplus⟩ ⟨-, hminus⟩
  linarith

/-- **The two halves exhaust the positive frames.** Nonvanishing of the
determinant is what leaves no third case. -/
theorem union_positiveFramesPlus_minus (hsig : HasSignatureTwo Q) {x₀ y₀ : M}
    (h₀ : IsPositiveFrame Q x₀ y₀) :
    positiveFrames Q =
      positiveFramesPlus Q x₀ y₀ ∪ positiveFramesMinus Q x₀ y₀ := by
  ext p
  constructor
  · intro hp
    rcases lt_or_gt_of_ne (pairingDet_ne_zero hsig h₀ hp) with hneg | hpos
    · exact Or.inr ⟨hp, hneg⟩
    · exact Or.inl ⟨hp, hpos⟩
  · rintro (⟨hp, -⟩ | ⟨hp, -⟩) <;> exact hp

omit [FiniteDimensional ℝ M] in
/-- **Swapping a pair moves it to the other half.** So neither half is vacuous
once one positive frame exists, and the split is a genuine two-way split. -/
theorem swap_mem_of_mem_positiveFramesPlus {x₀ y₀ : M} {p : M × M}
    (hp : p ∈ positiveFramesPlus Q x₀ y₀) :
    (p.2, p.1) ∈ positiveFramesMinus Q x₀ y₀ := by
  obtain ⟨hpair, hdet⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [IsPositiveFrame, framePlane, pairSpan, Set.pair_comm]
    exact hpair
  · rw [pairingDet_swap]
    linarith

end Halves

end PeriodDomain
