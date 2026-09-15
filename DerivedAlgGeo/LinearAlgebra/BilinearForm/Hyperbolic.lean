/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Ring

/-!
# The hyperbolic extension of a bilinear module

Given a module `M` over a commutative ring `R` carrying an `R`-bilinear form
`b`, the **hyperbolic extension** is `R × M × R` with

```
⟪(r, c, s), (r', c', s')⟫ = b c c' - r * s' - r' * s.
```

This is abstract bilinear-form algebra and nothing else. It is built from
Mathlib's `LinearMap.BilinMap` API, so by definition site it lives beside that
API rather than with any application of it, and it is importable without the
Mukai lattice, without stability and without schemes.

## This file owns the definition; it does not own the interpretation

`Lattice/Mukai/Basic.lean` takes `R = ℤ` and calls the result the Mukai
extension, because `N = NS(X)` with the intersection form recovers the
algebraic Mukai lattice. That identification is geometry: it needs
`D^b(Coh X)`, Chern characters and Hirzebruch--Riemann--Roch, none of which
exist in Mathlib at the pin. **Nothing here asserts or depends on it.**
Spherical-class vocabulary and the expected moduli dimension are application
words sitting on this carrier, and they stay with the application.

`Mukai/RealForm.lean` takes `R = ℝ` and bundles the result as a quadratic form
for the signature theory; `realPairing` is an `abbrev` for `pairing` there.

## The generalisation is over the coefficient ring, never over the dimension

The arity is fixed at three. A dimension-indexed self-pairing vanishes
identically in odd degree, so the threefold discriminant could not reach it;
that is recorded as a negative result in
`docs/architecture/abstraction-tree.md`. The reason the ring has to be
arbitrary at all is that three of the seven discriminant leaves this parents
are `ℚ`- or `A`-valued rather than `ℝ`-valued.

The declaration names are unchanged by the move to this file, and so is the
`Mukai` namespace. A namespace cutover would invalidate the immutable review
payloads that `exe/RestateHistoricalNames.lean` exists to protect, and this
file is a change of owner, not of vocabulary.
-/

namespace Mukai

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (b : M →ₗ[R] M →ₗ[R] R)

/-- The Mukai pairing built from a bilinear form `b` on the middle summand. -/
def pairing (v w : R × M × R) : R :=
  b v.2.1 w.2.1 - v.1 * w.2.2 - w.1 * v.2.2

@[simp]
theorem pairing_mk (r : R) (c : M) (s : R) (r' : R) (c' : M) (s' : R) :
    pairing b (r, c, s) (r', c', s') = b c c' - r * s' - r' * s :=
  rfl

/-- Symmetry of the extension, from symmetry of `b`. -/
theorem pairing_comm (hb : ∀ x y : M, b x y = b y x) (v w : R × M × R) :
    pairing b v w = pairing b w v := by
  simp only [pairing]
  rw [hb v.2.1 w.2.1]
  ring

/-! ### The quadratic refinement -/

/-- `⟪v, v⟫`. -/
def selfPairing (v : R × M × R) : R := pairing b v v

theorem selfPairing_eq_pairing (v : R × M × R) :
    selfPairing b v = pairing b v v :=
  rfl

/-- **The discriminant, once.**  `Δ(r, c, s) = b c c - 2 r s` is what every
discriminant in the repository projects to; the leaves differ only in which
ring `R` is, which bilinear form `b` is, and which three quantities are fed in.
-/
@[simp]
theorem selfPairing_mk (r : R) (c : M) (s : R) :
    selfPairing b (r, c, s) = b c c - 2 * (r * s) := by
  simp only [selfPairing, pairing_mk]
  ring

end Mukai
