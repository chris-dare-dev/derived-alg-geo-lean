/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.RealForm

/-!
# The exponential chart `exp(β + iω)` on the real Mukai extension

`exp(β + iω) = (1, β + iω, (β + iω)² / 2)` has real and imaginary parts `expRe`
and `expIm`. The computation that matters is three lines of pairing arithmetic:

```
⟪expRe, expRe⟫ = ⟪expIm, expIm⟫ = b ω ω,   ⟪expRe, expIm⟫ = 0,
```

so **as soon as `ω` has positive square the pair spans a positive plane**
(`isPositiveFrame_exp`) — the chart lands in the period domain, and `β` is
unconstrained. This is the distinguished family
`QuadraticForm/PositiveFrame.lean` says is needed to name Bridgeland's component
rather than an arbitrary half: take `(expRe, expIm)` as the reference pair.

## Why this is charge construction and not extension algebra

The carrier is not defined here and neither is the frame API. `RealExtension`,
`realPairing` and `realForm` — with the halving convention that makes
`⟪δ, δ⟫ = -2` read unchanged — are owned by
`LinearAlgebra/Lattice/Mukai/RealForm.lean`, and `IsPositiveFrame`,
`pairingDet` and `positiveFramesPlus` are owned by
`LinearAlgebra/QuadraticForm/PositiveFrame.lean`. Both stay where they are.

What this file adds is a **choice**: one distinguished positive frame out of
the many the extension admits, singled out because a central charge is wanted.
That choice is an input to `Z(β,ω)` and to nothing else in the extension
algebra, which is why the cutover ledger's row 03 puts the chart with the
numerical central-charge construction rather than with the quadratic extension.

Keeping it here is also what unblocks the split. `RealForm.lean` is upstream of
the neutral charge root `LinearAlgebra/BilinearForm/HodgeIndex.lean`, whose
transitive closure may contain neither stability conditions nor geometry, so
the carrier cannot follow the chart; and `Mukai.expCharge` consumes the chart
while `CentralCharge/Quadratic.lean` consumes `expCharge`, so the chart cannot
land in `Quadratic.lean` either. A separate module below `CentralCharge/` is
the placement both constraints allow.

Per the ledger's first standing decision the namespace does not move: these are
`Mukai.expRe` and `Mukai.isPositiveFrame_exp` at their new path, exactly as the
immutable payloads in `exe/RestateHistoricalNames.lean` spell them.

`V` is an arbitrary real bilinear space; no geometry is asserted.
-/

open QuadraticMap

namespace Mukai

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V)


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
theorem isPositiveFrame_exp (hb : ∀ x y : V, b x y = b y x) (hω : 0 < b ω ω) :
    PeriodDomain.IsPositiveFrame (realForm b) (expRe b β ω) (expIm b β ω) := by
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
    rw [PeriodDomain.framePlane_mk, PeriodDomain.pairSpan, hrange]
    simpa using finrank_span_eq_card hindep
  · rintro ⟨v, hv⟩ hv0
    rw [PeriodDomain.framePlane_mk, PeriodDomain.pairSpan, Submodule.mem_span_pair] at hv
    obtain ⟨s, t, rfl⟩ := hv
    rw [restrict_apply, realForm_smul_add_smul b β ω hb]
    have hst : s ≠ 0 ∨ t ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (Subtype.ext (by simp [hcon.1, hcon.2]))
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
theorem mem_positiveFramesPlus_exp (hb : ∀ x y : V, b x y = b y x) (hω : 0 < b ω ω) :
    (expRe b β ω, expIm b β ω) ∈
      PeriodDomain.positiveFramesPlus (realForm b) (expRe b β ω) (expIm b β ω) := by
  refine ⟨isPositiveFrame_exp b β ω hb hω, ?_⟩
  rw [pairingDet_exp_self b β ω hb]
  positivity


end Mukai
