/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.Orientation

/-!
# The real Mukai extension as a bundled quadratic form, and the exponential chart

`Lattice/Mukai/Basic.lean` builds the Mukai extension of a symmetric bilinear
`ℤ`-lattice as a bare pairing. `QuadraticForm/PeriodDomain.lean` and its
successors work with a bundled `QuadraticForm ℝ M`, because Mathlib's signature
theory is quadratic-form-native. This file is the bridge: the real Mukai
extension `ℝ × V × ℝ` of a real bilinear space, bundled, together with the
vectors that make it useful.

## The normalisation, which is the whole point of the file

The Mukai pairing is `⟪(r,c,s), (r',c',s')⟫ = b c c' - r s' - r' s`, and a
spherical class has `⟪δ, δ⟫ = -2`. The quadratic form here is **half** the
self-pairing,

```
realForm b (r, c, s) = (b c c - 2 * r * s) / 2,
```

so that `polar (realForm b) = realPairing b` on the nose — `polar_realForm`.
That is the convention `PeriodDomain.IsSphericalClass` is stated in, and with it
`⟪δ, δ⟫ = -2` reads unchanged.

**Building `toQuadraticMap` of the pairing itself instead would be a silent
factor-of-two error**: its polar form is twice the pairing, so `⟪δ,δ⟫ = -2`
would come out as `IsSphericalClass` for classes of self-pairing `-1`. The
halving is also the classical convention for an even lattice, where it is the
integral one.

Signatures are unaffected: scaling a form by a positive constant does not move
its positive or negative definite subspaces, so `sigPos` and `sigNeg` are the
same for `realForm b` and for the pairing.

## The exponential chart

`exp(β + iω) = (1, β + iω, (β + iω)² / 2)` has real and imaginary parts
`expRe` and `expIm`. The computation that matters is three lines of pairing
arithmetic:

```
⟪expRe, expRe⟫ = ⟪expIm, expIm⟫ = b ω ω,   ⟪expRe, expIm⟫ = 0,
```

so **as soon as `ω` has positive square the pair spans a positive plane**
(`isPositivePair_exp`) — the exponential chart lands in the period domain, and
`β` is unconstrained. This is the distinguished family
`QuadraticForm/Orientation.lean` says is needed to name Bridgeland's component
rather than an arbitrary half: take `(expRe, expIm)` as the reference pair.

## What is not here

* **The integral comparison.** Relating this to `Mukai.pairing` on
  `MukaiLattice N` needs `N ⊗ ℝ` and a compatible embedding; it is a separate
  step and nothing below depends on it.
* **The signature.** `HasSignatureTwo (realForm b)` when `b` has signature
  `(1, n - 1)` — the Hodge-index input — needs additivity of the signature over
  an orthogonal direct sum, which the pinned Mathlib does not have. Stated
  nowhere below; `isPositivePair_exp` deliberately needs only `0 < b ω ω`.
* **Any geometry.** `V` is an arbitrary real bilinear space, not `NS(X) ⊗ ℝ`.
-/

open QuadraticMap

namespace Mukai

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The real Mukai extension `ℝ ⊕ V ⊕ ℝ`.

The wall arithmetic in
`CategoryTheory/Triangulated/StabilityCondition/Walls/Spherical/Basic.lean` used
to declare this type and its pairing a second time, as `RealMukai`, and this
docstring named that copy rather than the file importing this one. It now
imports it. -/
abbrev RealExtension (V : Type*) : Type _ := ℝ × V × ℝ

variable (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- The Mukai pairing of the real extension. -/
def realPairing (v w : RealExtension V) : ℝ :=
  b v.2.1 w.2.1 - v.1 * w.2.2 - w.1 * v.2.2

@[simp]
theorem realPairing_apply (r : ℝ) (c : V) (s : ℝ) (r' : ℝ) (c' : V) (s' : ℝ) :
    realPairing b (r, c, s) (r', c', s') = b c c' - r * s' - r' * s := rfl

theorem realPairing_comm (hb : ∀ x y : V, b x y = b y x) (v w : RealExtension V) :
    realPairing b v w = realPairing b w v := by
  simp only [realPairing, hb v.2.1 w.2.1]
  ring

/-- The pairing, bundled. -/
def realBilin : LinearMap.BilinForm ℝ (RealExtension V) :=
  LinearMap.mk₂ ℝ (realPairing b)
    (fun v₁ v₂ w => by simp [realPairing]; ring)
    (fun a v w => by simp [realPairing]; ring)
    (fun v w₁ w₂ => by simp [realPairing]; ring)
    (fun a v w => by simp [realPairing]; ring)

@[simp]
theorem realBilin_apply (v w : RealExtension V) : realBilin b v w = realPairing b v w := rfl

/-- **The quadratic form of the real Mukai extension: half the self-pairing.**
The halving is what makes `polar (realForm b) = realPairing b`; see the module
docstring for why the other choice is a factor-of-two trap. -/
noncomputable def realForm : QuadraticForm ℝ (RealExtension V) :=
  ((1 / 2 : ℝ) • realBilin b).toQuadraticMap

theorem realForm_apply (v : RealExtension V) : realForm b v = realPairing b v v / 2 := by
  simp [realForm, LinearMap.BilinMap.toQuadraticMap_apply]
  ring

theorem realForm_mk (r : ℝ) (c : V) (s : ℝ) :
    realForm b (r, c, s) = (b c c - 2 * r * s) / 2 := by
  rw [realForm_apply, realPairing_apply]
  ring

/-- **The polar form of `realForm` is the Mukai pairing itself.** This is the
statement the normalisation exists for. -/
theorem polar_realForm (hb : ∀ x y : V, b x y = b y x) (v w : RealExtension V) :
    polar (⇑(realForm b)) v w = realPairing b v w := by
  rw [realForm, LinearMap.BilinMap.polar_toQuadraticMap]
  simp only [LinearMap.smul_apply, realBilin_apply, smul_eq_mul]
  rw [realPairing_comm b hb w v]
  ring

section Exponential

variable (β ω : V)

/-- The real part of `exp(β + iω)`. -/
noncomputable def expRe : RealExtension V := (1, β, (b β β - b ω ω) / 2)

/-- The imaginary part of `exp(β + iω)`. -/
noncomputable def expIm : RealExtension V := (0, ω, b β ω)

@[simp]
theorem realPairing_expRe_expRe : realPairing b (expRe b β ω) (expRe b β ω) = b ω ω := by
  simp [expRe, realPairing]
  ring

@[simp]
theorem realPairing_expIm_expIm : realPairing b (expIm b β ω) (expIm b β ω) = b ω ω := by
  simp [expIm, realPairing]

@[simp]
theorem realPairing_expRe_expIm : realPairing b (expRe b β ω) (expIm b β ω) = 0 := by
  simp [expRe, expIm, realPairing]

@[simp]
theorem realPairing_expIm_expRe (hb : ∀ x y : V, b x y = b y x) :
    realPairing b (expIm b β ω) (expRe b β ω) = 0 := by
  rw [← realPairing_comm b hb, realPairing_expRe_expIm]

/-- The value of `realForm` on a combination of the two exponential vectors: the
pair is orthogonal with equal square, so the form is a positive multiple of
`s ^ 2 + t ^ 2`. -/
theorem realForm_smul_add_smul (hb : ∀ x y : V, b x y = b y x) (s t : ℝ) :
    realForm b (s • expRe b β ω + t • expIm b β ω) = (s ^ 2 + t ^ 2) * b ω ω / 2 := by
  have hexp : realForm b (s • expRe b β ω + t • expIm b β ω)
      = realPairing b (s • expRe b β ω + t • expIm b β ω)
          (s • expRe b β ω + t • expIm b β ω) / 2 := realForm_apply b _
  rw [hexp]
  have hbil : realPairing b (s • expRe b β ω + t • expIm b β ω)
      (s • expRe b β ω + t • expIm b β ω)
      = s * s * realPairing b (expRe b β ω) (expRe b β ω)
        + s * t * realPairing b (expRe b β ω) (expIm b β ω)
        + t * s * realPairing b (expIm b β ω) (expRe b β ω)
        + t * t * realPairing b (expIm b β ω) (expIm b β ω) := by
    simp only [← realBilin_apply, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [hbil, realPairing_expRe_expRe, realPairing_expIm_expIm, realPairing_expRe_expIm,
    realPairing_expIm_expRe b β ω hb]
  ring

theorem expRe_ne_zero : expRe b β ω ≠ 0 := by
  intro h
  have : (expRe b β ω).1 = 0 := by rw [h]; rfl
  simp [expRe] at this

/-- **The exponential chart lands in the period domain.**

Only `0 < b ω ω` is needed; `β` is unconstrained, and no signature hypothesis is
used. The two vectors are orthogonal with equal positive square, so every
nonzero combination has positive square, and they are independent because their
rank coordinates are `1` and `0`. -/
theorem isPositivePair_exp (hb : ∀ x y : V, b x y = b y x) (hω : 0 < b ω ω) :
    PeriodDomain.IsPositivePair (realForm b) (expRe b β ω) (expIm b β ω) := by
  have hindep : LinearIndependent ℝ ![expRe b β ω, expIm b β ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hfst : s = 0 := by
      have h1 : (s • expRe b β ω + t • expIm b β ω).1 = 0 := by rw [hst]; rfl
      simpa [expRe, expIm] using h1
    refine ⟨hfst, ?_⟩
    by_contra ht
    have hval := realForm_smul_add_smul b β ω hb s t
    rw [hst, map_zero, hfst] at hval
    have hpos : 0 < (0 ^ 2 + t ^ 2) * b ω ω / 2 := by positivity
    rw [← hval] at hpos
    exact lt_irrefl _ hpos
  constructor
  · have hrange : ({expRe b β ω, expIm b β ω} : Set (RealExtension V))
        = Set.range ![expRe b β ω, expIm b β ω] := by
      ext z
      simp
      tauto
    rw [PeriodDomain.pairSpan, hrange]
    simpa using finrank_span_eq_card hindep
  · rintro ⟨v, hv⟩ hv0
    rw [PeriodDomain.pairSpan, Submodule.mem_span_pair] at hv
    obtain ⟨s, t, rfl⟩ := hv
    rw [restrict_apply, realForm_smul_add_smul b β ω hb]
    have hst : s ≠ 0 ∨ t ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (by simp [hcon.1, hcon.2])
    rcases hst with hs | ht
    · have : 0 < s ^ 2 := by positivity
      have h2 : 0 ≤ t ^ 2 := sq_nonneg t
      nlinarith
    · have : 0 < t ^ 2 := by positivity
      have h2 : 0 ≤ s ^ 2 := sq_nonneg s
      nlinarith

/-- The pairing determinant of the exponential pair against itself is
`(b ω ω) ^ 2`: the pair is orthogonal with equal square, so the off-diagonal
term drops. -/
theorem pairingDet_exp_self (hb : ∀ x y : V, b x y = b y x) :
    PeriodDomain.pairingDet (realForm b) (expRe b β ω) (expIm b β ω)
      (expRe b β ω) (expIm b β ω) = (b ω ω) ^ 2 := by
  rw [PeriodDomain.pairingDet, polar_realForm b hb, polar_realForm b hb, polar_realForm b hb,
    polar_realForm b hb, realPairing_expRe_expRe, realPairing_expIm_expIm,
    realPairing_expRe_expIm, realPairing_expIm_expRe b β ω hb]
  ring

/-- **The exponential pair lies in its own positive half.**

Taking `(expRe, expIm)` as the reference is therefore not an arbitrary choice
dressed up: the half it names is the one containing `exp(β + iω)`, which is how
Bridgeland specifies `P⁺`. Whether that half is independent of `ω` is the
cocycle question, and is not settled here. -/
theorem mem_periodDomainPlus_exp (hb : ∀ x y : V, b x y = b y x) (hω : 0 < b ω ω) :
    (expRe b β ω, expIm b β ω) ∈
      PeriodDomain.periodDomainPlus (realForm b) (expRe b β ω) (expIm b β ω) := by
  refine ⟨isPositivePair_exp b β ω hb hω, ?_⟩
  rw [pairingDet_exp_self b β ω hb]
  positivity

end Exponential

end Mukai
