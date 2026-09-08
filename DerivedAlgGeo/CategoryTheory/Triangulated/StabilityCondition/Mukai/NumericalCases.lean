/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Charge
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.ChargePositivity

/-!
# The four cases of Lemma 6.2, at the level of the charge

`ChargePositivity.lean` proves the two analytic facts Bridgeland's Lemma 6.2
(`math/0307164`, §6) needs: `im_expCharge_pos` for the cases that stay off the
real axis, and `re_expCharge_pos_of_nonneg` / `re_expCharge_pos_of_neg_one` for
the boundary. Neither says anything about `semiClosedUpperHalfPlane`, which is
the set a `StabilityFunction`'s `nonzero_mem` field actually mentions.

This file closes that gap and no other: each case of Lemma 6.2 is turned into a
membership statement, **with the shift applied where the paper applies it**.

## The sign trap, which no gate catches

Bridgeland states every sign in §6 for the **sheaf**, not for the object of the
tilted heart. In the boundary case `E` is torsion-free with `μ_ω(E) = β·ω`, so
`E ∈ F(β)` and the object of `𝒜(β,ω)` is **`E⟦1⟧`**, whose class is `-v(E)` and
whose charge is `-Z(E)`.

So `ChargePositivity` concluding `Re Z(E) > 0` is exactly what puts the *heart
object* on the negative real axis, which is the `{z | z.im = 0 ∧ z.re < 0}` half
of `semiClosedUpperHalfPlane`. The two apparent reversals cancel. Getting this
backwards yields a false statement that compiles, which is why the shifted cases
below are stated on `-v` explicitly rather than left to the caller.

## What this is not

**It is not Lemma 6.2**, and it is deliberately not wired into
`MukaiChargeData`. `Mukai.Charge` says why, and the reason stands: bundling
these case discriminants as fields of that structure would make `nonzero_mem` a
one-line case split over invented assumptions — it would compile, pass every
gate, and prove nothing. Lemma 6.2 requires *proving* which objects of the
tilted heart fall into which case, from `hnTilt_heart_iff`,
`mem_hnTors_of_rank_zero` and `degree_pos_of_rank_zero`. That work is not here.

What is here is the other half: once an object is known to be in a given case,
this is the arithmetic that puts its charge in the half plane. Every one of the
statements below is a fact about a triple of reals and a vector; no sheaf, no
heart, no torsion pair, no K3 surface appears.

## The four cases

With `v = (r, c, s)`, writing `Im Z = ω·(c - r•β)`:

| case | hypothesis | conclusion |
|---|---|---|
| curve torsion, or free above the cutoff | `0 < ω·(c - r•β)` | `Z v` upper half plane |
| torsion in dimension zero | `r = 0`, `c = 0`, `0 < s` | `Z v` negative real axis |
| torsion-free below the cutoff | `ω·(c - r•β) < 0` | `Z (-v)` upper half plane |
| the boundary | `ω·(c - r•β) = 0`, Hodge index, Bogomolov | `Z (-v)` negative real axis |

The first and third are the same fact read at `v` and at `-v`; they are stated
separately because the caller reaches them from opposite sides of the cutoff.

## Main results

`Mukai.expCharge_neg` — `Z(-v) = -Z(v)`, what the shift costs — is derived
upstream from `Mukai.expChargeHom` in the numerical Mukai layer.

* `mem_semiClosedUpperHalfPlane_of_apply_sub_smul_pos` — cases 1 and 3.
* `mem_semiClosedUpperHalfPlane_of_dimension_zero` — case 2.
* `neg_mem_semiClosedUpperHalfPlane_of_apply_sub_smul_neg` — below the cutoff.
* `neg_mem_semiClosedUpperHalfPlane_of_boundary_of_nonneg` and
  `…_of_neg_one` — the boundary, non-spherical and spherical.
* `neg_sum_mem_semiClosedUpperHalfPlane_of_boundary_of_neg_one` — the
  assembly-safe factorwise boundary case.
-/

open Complex QuadraticMap
open scoped BigOperators

namespace CategoryTheory.Triangulated

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V)

/-! ### Membership, from the two analytic shapes -/

/-- A charge with positive imaginary part is in the half plane. -/
theorem mem_semiClosedUpperHalfPlane_of_im_pos {z : ℂ} (h : 0 < z.im) :
    z ∈ semiClosedUpperHalfPlane := Or.inl h

/-- A charge on the negative real axis is in the half plane. -/
theorem mem_semiClosedUpperHalfPlane_of_im_zero_of_re_neg {z : ℂ}
    (him : z.im = 0) (hre : z.re < 0) : z ∈ semiClosedUpperHalfPlane :=
  Or.inr ⟨him, hre⟩

/-! ### Cases 1 and 3: strictly above the cutoff -/

/-- **Cases 1 and 3 of Lemma 6.2.** A class meeting `ω` strictly positively
after the cutoff shift has its charge in the open upper half plane.

Torsion supported on a curve and a torsion-free sheaf of slope strictly above
`β·ω` reach this from different geometry, but the arithmetic is the same one
line, which is why they share a statement. -/
theorem mem_semiClosedUpperHalfPlane_of_apply_sub_smul_pos
    (hb : ∀ x y : V, b x y = b y x) {r : ℝ} {c : V} {s : ℝ}
    (h : 0 < b ω (c - r • β)) :
    Mukai.expCharge b β ω (r, c, s) ∈ semiClosedUpperHalfPlane :=
  mem_semiClosedUpperHalfPlane_of_im_pos (Mukai.im_expCharge_pos b β ω hb h)

/-! ### Case 2: torsion in dimension zero -/

/-- **Case 2 of Lemma 6.2.** A class `(0, 0, s)` with `0 < s` — the numerical
shadow of a torsion sheaf supported in dimension zero, where `s` is the length —
has charge `-s`, on the negative real axis.

Note this case does **not** go through `ω` at all: both coordinates that could
see the polarisation vanish, and the conclusion is an evaluation rather than an
inequality about the form. -/
theorem mem_semiClosedUpperHalfPlane_of_dimension_zero
    (hb : ∀ x y : V, b x y = b y x) {s : ℝ} (hs : 0 < s) :
    Mukai.expCharge b β ω ((0 : ℝ), (0 : V), s) ∈ semiClosedUpperHalfPlane := by
  refine mem_semiClosedUpperHalfPlane_of_im_zero_of_re_neg ?_ ?_
  · rw [Mukai.im_expCharge b β ω hb]; simp
  · rw [Mukai.expCharge_apply b β ω hb]; simpa using hs

/-! ### Case 3 shifted, and case 4: at or below the cutoff

Below, `v` is the class of the **sheaf** and the object of the tilted heart is
its shift, so every conclusion is about `-v`. -/

/-- **Strictly below the cutoff.** A torsion-free sheaf with `μ_ω(E) < β·ω` lies
in `F(β)`, so `E⟦1⟧` is the heart object; its charge has positive imaginary
part. -/
theorem neg_mem_semiClosedUpperHalfPlane_of_apply_sub_smul_neg
    (hb : ∀ x y : V, b x y = b y x) {r : ℝ} {c : V} {s : ℝ}
    (h : b ω (c - r • β) < 0) :
    Mukai.expCharge b β ω (-(r, c, s)) ∈ semiClosedUpperHalfPlane := by
  refine mem_semiClosedUpperHalfPlane_of_im_pos ?_
  rw [Mukai.expCharge_neg b β ω, Complex.neg_im,
    Mukai.im_expCharge_eq_apply_sub_smul b β ω hb]
  linarith

section Boundary

variable [FiniteDimensional ℝ V]

/-- **The boundary, non-spherical case.** `μ_ω(E) = β·ω` and `v(E)² ≥ 0`, so
`Re Z(E) > 0` and the heart object `E⟦1⟧` sits on the negative real axis.

`hv` is the Mukai-square input. In this repository's halved convention
`realForm b v ≥ 0` is the paper's `v(E)² ≥ 0`. -/
theorem neg_mem_semiClosedUpperHalfPlane_of_boundary_of_nonneg
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1) (hω : 0 < b ω ω)
    {r : ℝ} (hr : 0 < r) {c : V} {s : ℝ}
    (him : (Mukai.expCharge b β ω (r, c, s)).im = 0)
    (hv : 0 ≤ Mukai.realForm b (r, c, s)) :
    Mukai.expCharge b β ω (-(r, c, s)) ∈ semiClosedUpperHalfPlane := by
  have hre := Mukai.re_expCharge_pos_of_nonneg b β ω hb hsigPos hω hr him hv
  refine mem_semiClosedUpperHalfPlane_of_im_zero_of_re_neg ?_ ?_ <;>
    rw [Mukai.expCharge_neg b β ω]
  · rw [Complex.neg_im, him, neg_zero]
  · rw [Complex.neg_re]; linarith

/-- **The boundary, spherical case.** `v(E)² = -2` in the paper — `realForm = -1`
here — still gives `Re Z(E) > 0`, but now needs `ω² > 2`, and that is enough only
because `r` is an integer rank, so `1 ≤ r`.

This is the case Bridgeland's hypothesis "for all spherical sheaves `E` one has
`Z(E) ∉ ℝ_{⩽0}`" exists to rule out, and `ω² > 2` is his sufficient condition
for it. -/
theorem neg_mem_semiClosedUpperHalfPlane_of_boundary_of_neg_one
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1) (hω : 2 < b ω ω)
    {r : ℝ} (hr : 1 ≤ r) {c : V} {s : ℝ}
    (him : (Mukai.expCharge b β ω (r, c, s)).im = 0)
    (hv : -1 ≤ Mukai.realForm b (r, c, s)) :
    Mukai.expCharge b β ω (-(r, c, s)) ∈ semiClosedUpperHalfPlane := by
  have hre := Mukai.re_expCharge_pos_of_neg_one b β ω hb hsigPos hω hr him hv
  refine mem_semiClosedUpperHalfPlane_of_im_zero_of_re_neg ?_ ?_ <;>
    rw [Mukai.expCharge_neg b β ω]
  · rw [Complex.neg_im, him, neg_zero]
  · rw [Complex.neg_re]; linarith

/-- **The boundary case assembled factorwise.**

Every member of a nonempty finite family lies on the boundary, has positive
rank, and satisfies the stable-factor Mukai-square bound.  Each unshifted
charge therefore has positive real part and zero imaginary part, so the charge
of the negative of their sum lies on the allowed negative real ray.

This is the assembly-safe form of the boundary argument: the bound
`-1 ≤ realForm b (v i)` is required for each factor, never for their sum.  The
latter condition is not additive. -/
theorem neg_sum_mem_semiClosedUpperHalfPlane_of_boundary_of_neg_one
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1) (hω : 2 < b ω ω)
    {n : ℕ} (hn : 0 < n) (v : Fin n → Mukai.RealExtension V)
    (hr : ∀ i, 1 ≤ (v i).1)
    (him : ∀ i, (Mukai.expCharge b β ω (v i)).im = 0)
    (hv : ∀ i, -1 ≤ Mukai.realForm b (v i)) :
    Mukai.expCharge b β ω (-(∑ i, v i)) ∈ semiClosedUpperHalfPlane := by
  classical
  let i₀ : Fin n := ⟨0, hn⟩
  have hre : ∀ i, 0 < (Mukai.expCharge b β ω (v i)).re := fun i ↦
    Mukai.re_expCharge_pos_of_neg_one b β ω hb hsigPos hω (hr i) (him i) (hv i)
  have hcharge_sum :
      Mukai.expCharge b β ω (∑ i, v i) = ∑ i, Mukai.expCharge b β ω (v i) := by
    simpa only [Mukai.expChargeHom_apply] using
      map_sum (Mukai.expChargeHom b β ω) v Finset.univ
  refine mem_semiClosedUpperHalfPlane_of_im_zero_of_re_neg ?_ ?_
  · rw [Mukai.expCharge_neg b β ω, Complex.neg_im, hcharge_sum]
    have him_sum : (∑ i, Mukai.expCharge b β ω (v i)).im =
        ∑ i, (Mukai.expCharge b β ω (v i)).im := by
      simpa only [show ∀ z : ℂ, Complex.imAddGroupHom z = z.im from fun _ ↦ rfl] using
        map_sum Complex.imAddGroupHom (fun i ↦ Mukai.expCharge b β ω (v i)) Finset.univ
    rw [him_sum]
    simp [him]
  · rw [Mukai.expCharge_neg b β ω, Complex.neg_re, hcharge_sum]
    have hre_sum : (∑ i, Mukai.expCharge b β ω (v i)).re =
        ∑ i, (Mukai.expCharge b β ω (v i)).re := by
      simpa only [show ∀ z : ℂ, Complex.reAddGroupHom z = z.re from fun _ ↦ rfl] using
        map_sum Complex.reAddGroupHom (fun i ↦ Mukai.expCharge b β ω (v i)) Finset.univ
    rw [hre_sum]
    exact neg_neg_of_pos (Finset.sum_pos (fun i _ ↦ hre i) ⟨i₀, Finset.mem_univ i₀⟩)

end Boundary

end CategoryTheory.Triangulated
