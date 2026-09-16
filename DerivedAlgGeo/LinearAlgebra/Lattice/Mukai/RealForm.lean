/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.Basic
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PositiveFrame

/-!
# The real Mukai extension as a bundled quadratic form, and the exponential chart

`Lattice/Mukai/Basic.lean` builds the Mukai extension of a symmetric bilinear
`ℤ`-lattice as a bare pairing. `QuadraticForm/PositivePlane.lean` and its
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

## The exponential chart is not here

`expRe`, `expIm` and `isPositiveFrame_exp` used to sit below the pairing
lemmas. They are a *choice* of one distinguished positive frame, made because a
central charge is wanted, and the cutover ledger's row 03 puts that choice with
the numerical central-charge construction rather than with the quadratic
extension. They now live in
`CategoryTheory/Triangulated/StabilityCondition/CentralCharge/Mukai/Chart.lean`,
keeping the `Mukai` namespace.

The carrier could not follow them. This file is upstream of the neutral charge
root `LinearAlgebra/BilinearForm/HodgeIndex.lean`, by way of
`RealFormSignature.lean`, and that root's transitive closure may contain neither
stability conditions nor geometry. Severing the chart is what let the row move
at all.

## The graded pairing is this pairing, and the `∫H²` weight is real

An abstraction audit proposed a graded form `-∑_k (-1)^k v_k w_{n-k}` on
`Fin (n + 1) → ℝ`, together with a parity theorem about it. At `n = 2` that form
is the one already here: both it and `b c c' - r s' - r' s` expand to
`v₁w₁ - v₀w₂ - v₂w₀`, with no weight, no transport and no hypothesis.
`realPairing_mul_eq_alternatingSum` records that, so the graded form is never
declared a second owner of the even case. Nothing new is defined here; these are
theorems about `realPairing`, `realForm` and `selfPairing`.

The compression `v ↦ (∫H²·rk, ∫H·c₁, ch₂)` relates the two on the rank-one
slice `c = x • H`, and `realPairing_compression_rankOne` carries the weight
`∫H² = b H H` explicitly rather than absorbing it.

### Three unifications that are refuted, and why a graded form still earns `n ≠ 2`

* **Odd degree is alternating, and no `realPairing` is.** At odd `n` the graded
  form has `⟪v, v⟫ = 0` for every `v`, because the sum pairs slot `k` with slot
  `n - k` under opposite signs. No `realPairing b` can do that: `(1, 0, 1)` has
  `realPairing b (1,0,1) (1,0,1) = -2` for every `b`. So the odd case is not
  this pairing under any choice of `b`, and a separate graded form is what odd
  degree needs.
* **The `H`-compression is not injective once the Picard rank exceeds one.** It
  collapses any two classes whose `c₁` differ by something `H`-orthogonal, so a
  multi-divisor pairing does not factor through `Fin 3 → ℝ`. That is why the
  bridge below is stated on the rank-one slice `c = x • H` and not in general.
* **The weight is not removable.** `realPairing_compression_rankOne` carries
  `b H H` to the first power, and it is `1` exactly when `∫H² = 1`. Rescaling
  `H` rescales the weight rather than clearing it, so the two forms agree on the
  nose only under that normalisation.

## What is not here

* **The integral comparison.** Relating this to `Mukai.pairing` on
  `MukaiLattice N` needs `N ⊗ ℝ` and a compatible embedding; it is a separate
  step and nothing below depends on it.
* **The signature.** `HasSignatureTwo (realForm b)` when `b` has signature
  `(1, n - 1)` — the Hodge-index input — needs additivity of the signature over
  an orthogonal direct sum, which the pinned Mathlib does not have. Stated
  nowhere below; `isPositiveFrame_exp`, now downstream, deliberately needs
  only `0 < b ω ω`.
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

/-- **The Mukai pairing of the real extension is `Mukai.pairing` at `R = ℝ`.**

An `abbrev`, not a second definition: `RealExtension V` is `ℝ × V × ℝ` and
`Basic.lean`'s `pairing` is stated over an arbitrary coefficient ring, so this
is the same function under a name the real lane reads better. Every lemma below
is therefore a statement about the one root. -/
abbrev realPairing (v w : RealExtension V) : ℝ := pairing b v w

/-- Not a `simp` lemma: `pairing_mk` is already `simp` and `realPairing` is
reducible, so the two would be the same rewrite registered twice and the
normal-form linter rejects the duplicate. Kept as a named statement because the
real lane rewrites by it. -/
theorem realPairing_apply (r : ℝ) (c : V) (s : ℝ) (r' : ℝ) (c' : V) (s' : ℝ) :
    realPairing b (r, c, s) (r', c', s') = b c c' - r * s' - r' * s := rfl

theorem realPairing_comm (hb : ∀ x y : V, b x y = b y x) (v w : RealExtension V) :
    realPairing b v w = realPairing b w v :=
  pairing_comm b hb v w

/-- The pairing, bundled. -/
def realBilin : LinearMap.BilinForm ℝ (RealExtension V) :=
  LinearMap.mk₂ ℝ (realPairing b)
    (fun v₁ v₂ w => by simp [realPairing, pairing]; ring)
    (fun a v w => by simp [realPairing, pairing]; ring)
    (fun v w₁ w₂ => by simp [realPairing, pairing]; ring)
    (fun a v w => by simp [realPairing, pairing]; ring)

@[simp]
theorem realBilin_apply (v w : RealExtension V) : realBilin b v w = realPairing b v w := rfl

/-- **The discriminant of the real Mukai extension**, `Δ(r, c, s) = b c c - 2rs`.

This is the self-pairing as a bundled `QuadraticForm`, **without** the halving
of `realForm`: the discriminant convention of Macrì--Schmidt is the unhalved
one, and `realDiscriminant_eq_selfPairing` is what pins the choice.

It lives here rather than beside a divisor space because it parents the
divisorial discriminant leaves, and its former home imported two of them. `V`
is an arbitrary real bilinear space; the `DivisorSpace` spelling in
`Walls/Divisorial/Support.lean` is this form at `b = S.intersection`. -/
def realDiscriminant : QuadraticForm ℝ (RealExtension V) :=
  (realBilin b).toQuadraticMap

/-- **The bundled discriminant is the Mukai self-pairing.** The unhalved
convention is exactly what makes this an equality rather than a factor of two. -/
theorem realDiscriminant_eq_selfPairing (v : RealExtension V) :
    realDiscriminant b v = selfPairing b v := by
  rw [realDiscriminant, LinearMap.BilinMap.toQuadraticMap_apply, realBilin_apply]
  rfl

@[simp]
theorem realDiscriminant_mk (r : ℝ) (c : V) (s : ℝ) :
    realDiscriminant b (r, c, s) = b c c - 2 * r * s := by
  rw [realDiscriminant_eq_selfPairing, selfPairing_mk]
  ring

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

/-! ## The graded pairing, as theorems about this root

See the module docstring. No new declaration: the graded form is written out
where it is used, so that it never becomes a second name for `realPairing`. -/

/-- **The graded `n = 2` pairing is `realPairing` on the scalar line.**

The right-hand side is the audit's graded form `-∑_k (-1)^k d_k e_{2-k}` written
out. There is no weight, no hypothesis and no transport: at `n = 2` the two are
one equation, so the graded form must not be declared a second owner of the even
case. Odd degree is a different matter; see the module docstring. -/
theorem realPairing_mul_eq_alternatingSum (d e : Fin 3 → ℝ) :
    realPairing (LinearMap.mul ℝ ℝ) (d 0, d 1, d 2) (e 0, e 1, e 2)
      = -∑ k : Fin 3, (-1 : ℝ) ^ (k : ℕ) * d k * e k.rev := by
  have r0 : (0 : Fin 3).rev = 2 := rfl
  have r1 : (1 : Fin 3).rev = 1 := rfl
  have r2 : (2 : Fin 3).rev = 0 := rfl
  rw [realPairing_apply, Fin.sum_univ_three, r0, r1, r2]
  norm_num
  ring

/-- **The weighted rank-one bridge.** On the slice `c = x • H` the graded
pairing of the `H`-degree compressions `(∫H²·rk, ∫H·c₁, ch₂)` is `∫H²` times
this pairing.

The left-hand side is that graded pairing written out. The weight `b H H` is
first power and is not removable: it is `1` exactly when `∫H² = 1`. The
rank-one hypothesis is not decoration either, since the compression stops being
injective as soon as the Picard rank exceeds one. -/
theorem realPairing_compression_rankOne (H : V) (r x s r' x' s' : ℝ) :
    b H (x • H) * b H (x' • H) - b H H * r * s' - s * (b H H * r')
      = b H H * realPairing b (r, x • H, s) (r', x' • H, s') := by
  have h1 : b H (x • H) = x * b H H := by rw [map_smul, smul_eq_mul]
  have h2 : b H (x' • H) = x' * b H H := by rw [map_smul, smul_eq_mul]
  have h3 : b (x • H) (x' • H) = x * x' * b H H := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  rw [realPairing_apply, h1, h2, h3]
  ring

/-- **The factor of two is the `realForm` halving and nothing else.**

Specialising the bridge to `v = w` puts a `2` in front, and it is exactly the
`realForm = realPairing / 2` convention this file's module docstring calls a
factor-of-two trap — not a second discrepancy stacked on the `∫H²` weight. -/
theorem realForm_compression_rankOne (H : V) (r x s : ℝ) :
    b H (x • H) * b H (x • H) - b H H * r * s - s * (b H H * r)
      = 2 * b H H * realForm b (r, x • H, s) := by
  rw [realPairing_compression_rankOne b H r x s r x s, realForm_apply]
  ring


end Mukai
