/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

/-!
# Basic opens on a projective spectrum: two inclusions

A basic open `D₊(b)` lies inside `D₊(bⁿ)` for every `n`, and an open inside `D₊(a)` and `D₊(b)`
lies inside `D₊(a b)`. Both are statements about `ProjectiveSpectrum.basicOpen` alone. Neither
mentions a module sheaf, a twist, or a fraction.

## Main definitions

This file introduces no new definitions; it proves facts about Mathlib's
`ProjectiveSpectrum.basicOpen`.

## Main results

* `AlgebraicGeometry.Proj.basicOpen_le_basicOpen_pow`: `D₊(b) ≤ D₊(bⁿ)` for every `n`, including
  `n = 0`.
* `AlgebraicGeometry.Proj.le_basicOpen_mul`: an open inside `D₊(a)` and `D₊(b)` is inside
  `D₊(a b)`.

## Implementation notes

### `basicOpen_le_basicOpen_pow` is upstream-shaped

Mathlib has `ProjectiveSpectrum.basicOpen_pow`, an *equality* `D₊(bⁿ) = D₊(b)` requiring `0 < n`.
The inclusion `D₊(b) ≤ D₊(bⁿ)` needs no hypothesis on `n` at all: at `n = 0` the right-hand side is
everything. Consumers here want the inclusion and want it uniformly in `n`, because the exponent is
produced by a lemma rather than chosen, and carrying a `0 < n` side condition through the twist
bookkeeping costs more than the strengthening saves.

That makes it a candidate to propose upstream rather than a local convenience, which is why it is
here under its own name instead of inlined at its forty call sites.

## References

Mathlib's `ProjectiveSpectrum.basicOpen_pow` and `ProjectiveSpectrum.basicOpen_mul`.

## Tags

projective spectrum, basic open, graded ring
-/

open TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-- **A basic open is inside every basic open of a power of its element.**

An equality when the exponent is positive (`ProjectiveSpectrum.basicOpen_pow`), but the inclusion
is what the fraction API needs and it holds for `n = 0` too. -/
theorem basicOpen_le_basicOpen_pow (b : A) (n : ℕ) :
    ProjectiveSpectrum.basicOpen 𝒜 b ≤ ProjectiveSpectrum.basicOpen 𝒜 (b ^ n) := by
  intro x hx
  have hx' : b ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := hx
  exact Submonoid.pow_mem _ hx' n

/-- **An open inside two basic opens is inside the basic open of the product.** -/
theorem le_basicOpen_mul {U : Opens (ProjectiveSpectrum.top 𝒜)} {a b : A}
    (ha : U ≤ ProjectiveSpectrum.basicOpen 𝒜 a) (hb : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b) :
    U ≤ ProjectiveSpectrum.basicOpen 𝒜 (a * b) := by
  rw [ProjectiveSpectrum.basicOpen_mul]
  exact le_inf ha hb

end AlgebraicGeometry.Proj
