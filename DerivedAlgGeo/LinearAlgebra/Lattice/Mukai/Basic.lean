/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Arithmetic.TorsionFree
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The Mukai extension of a symmetric bilinear lattice

Given an additive group `N` carrying a symmetric `ℤ`-bilinear form `b`, the
**Mukai extension** is `ℤ × N × ℤ` with

```
⟪(r, c, s), (r', c', s')⟫ = b c c' - r * s' - r' * s.
```

**This is not the Mukai lattice of a K3 surface.** It is the abstract lattice
that lattice is an instance of. Taking `N = NS(X)` with the intersection form
recovers the algebraic Mukai lattice `H⁰ ⊕ NS ⊕ H⁴`, but that identification
needs `D^b(Coh X)`, Chern characters and Hirzebruch–Riemann–Roch, none of which
exist in Mathlib at the pin. It is geometry, it lives in the assumption
frontier, and nothing here discharges it or depends on it.

This is the same discipline `LinearAlgebra/Lattice/Numerical.lean` applies to
`Fin 2 → ℤ`:
every theorem below is a theorem about **an arbitrary symmetric bilinear
`ℤ`-lattice**, and is true whether or not any surface exists.

## Naming

`expectedDim v = ⟪v, v⟫ + 2` is a **definition**, not the Mukai dimension
theorem. The statement that a moduli space of stable objects with primitive
Mukai vector `v` has dimension `⟪v, v⟫ + 2` is geometry and is not asserted.
The name records which numerical quantity is being tracked, nothing more.

## Main results

* `pairing_comm` — the extension is symmetric when `b` is.
* `even_selfPairing` — the extension of an even lattice is even.
* `pairing_rankUnit_corankUnit` — the rank/co-rank plane is a hyperbolic plane:
  two isotropic generators pairing to `-1`.
-/

namespace Mukai

/-- The underlying group of the Mukai extension of `N`: triples `(r, c, s)`.

The name is suggestive of the K3 case; the module docstring records that the
identification with any geometric lattice is **not** made here. -/
abbrev MukaiLattice (N : Type*) : Type _ := ℤ × N × ℤ

/-! ### The pairing, over an arbitrary coefficient ring

**The generalisation is over the coefficient ring, never over the dimension.**
The arity is fixed at three. A dimension-indexed self-pairing vanishes
identically in odd degree, so the threefold discriminant could not reach it;
that is recorded as a negative result in
`docs/architecture/abstraction-tree.md`.

`MukaiLattice N` is the `R = ℤ` carrier and is unchanged, as is every `ℤ`-only
theorem below it. `Mukai/RealForm.lean`'s `RealExtension V` is the `R = ℝ`
carrier and `realPairing` is an `abbrev` for this definition there. The reason
the ring has to move at all is that three of the seven discriminant leaves this
parents are `ℚ`- or `A`-valued rather than `ℝ`-valued; that is the only thing a
`ℤ`-only root lacked, and no new declaration name is introduced to supply it.
-/

section CoefficientRing

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

/-! #### The quadratic refinement -/

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

end CoefficientRing

variable {N : Type*} [AddCommGroup N] (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ)

/-! ### Bilinearity

Proved directly from the definition rather than inherited, so that every
downstream rewrite has a named lemma to hit.

`linter.unusedSimpArgs` is disabled for this section, and the suppression is
load-bearing rather than cosmetic. It flags `LinearMap.add_apply` and its
siblings in the four *left*-hand lemmas as unused; removing them on that advice
makes all four fail. The reason is asymmetry in the definition: on the right,
`b u.2.1 (v.2.1 + w.2.1)` is closed by `map_add` on the applied form alone,
whereas on the left `b (u.2.1 + v.2.1) w.2.1` first becomes `(b u.2.1 + b v.2.1) w.2.1`
and needs `LinearMap.add_apply` to reach a goal `ring` can see. The linter
judges the `simp only` call in isolation and does not know a `ring` follows it.
Re-check this if the pin moves; do not delete the arguments on the warning
alone. -/

set_option linter.unusedSimpArgs false in
theorem pairing_add_left (u v w : MukaiLattice N) :
    pairing b (u + v) w = pairing b u w + pairing b v w := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
  ring

theorem pairing_add_right (u v w : MukaiLattice N) :
    pairing b u (v + w) = pairing b u v + pairing b u w := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, map_add]
  ring

set_option linter.unusedSimpArgs false in
theorem pairing_smul_left (a : ℤ) (v w : MukaiLattice N) :
    pairing b (a • v) w = a * pairing b v w := by
  simp only [pairing, Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  ring

theorem pairing_smul_right (a : ℤ) (v w : MukaiLattice N) :
    pairing b v (a • w) = a * pairing b v w := by
  simp only [pairing, Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul]
  ring

set_option linter.unusedSimpArgs false in
theorem pairing_neg_left (v w : MukaiLattice N) :
    pairing b (-v) w = -pairing b v w := by
  simp only [pairing, Prod.fst_neg, Prod.snd_neg, map_neg, LinearMap.neg_apply]
  ring

theorem pairing_neg_right (v w : MukaiLattice N) :
    pairing b v (-w) = -pairing b v w := by
  simp only [pairing, Prod.fst_neg, Prod.snd_neg, map_neg]
  ring

set_option linter.unusedSimpArgs false in
theorem pairing_sub_left (u v w : MukaiLattice N) :
    pairing b (u - v) w = pairing b u w - pairing b v w := by
  simp only [pairing, Prod.fst_sub, Prod.snd_sub, map_sub, LinearMap.sub_apply]
  ring

theorem pairing_sub_right (u v w : MukaiLattice N) :
    pairing b u (v - w) = pairing b u v - pairing b u w := by
  simp only [pairing, Prod.fst_sub, Prod.snd_sub, map_sub]
  ring

@[simp]
theorem pairing_zero_left (w : MukaiLattice N) : pairing b 0 w = 0 := by
  simp [pairing]

@[simp]
theorem pairing_zero_right (v : MukaiLattice N) : pairing b v 0 = 0 := by
  simp [pairing]

/-! ### The quadratic refinement, over `ℤ`

`selfPairing` itself is generic and lives above; these are the `ℤ`-lattice
facts about it. -/

theorem selfPairing_smul (a : ℤ) (v : MukaiLattice N) :
    selfPairing b (a • v) = a ^ 2 * selfPairing b v := by
  simp only [selfPairing_eq_pairing, pairing_smul_left, pairing_smul_right]
  ring

@[simp]
theorem selfPairing_zero : selfPairing b (0 : MukaiLattice N) = 0 := by
  simp [selfPairing_eq_pairing]

theorem selfPairing_neg (v : MukaiLattice N) :
    selfPairing b (-v) = selfPairing b v := by
  simp only [selfPairing_eq_pairing, pairing_neg_left, pairing_neg_right, neg_neg]

/-- The Mukai extension of an **even** lattice is even.

For a K3 surface the intersection form on `NS(X)` is even, and this is the
lattice-theoretic reason `⟪v, v⟫` is always even there. The hypothesis is
stated, never assumed from geometry. -/
theorem even_selfPairing (heven : ∀ x : N, Even (b x x)) (v : MukaiLattice N) :
    Even (selfPairing b v) := by
  obtain ⟨k, hk⟩ := heven v.2.1
  refine ⟨k - v.1 * v.2.2, ?_⟩
  simp only [selfPairing, pairing, hk]
  ring

/-! ### Distinguished classes

`IsSpherical` and `IsIsotropic` are the two numerical conditions the
wall-classification literature is organised around. Both are conditions on a
lattice vector alone. -/

/-- `⟪v, v⟫ = -2`. In the K3 case these are the classes of spherical objects;
here it is a numerical condition and nothing more. -/
def IsSpherical (v : MukaiLattice N) : Prop := selfPairing b v = -2

/-- `⟪v, v⟫ = 0`. -/
def IsIsotropic (v : MukaiLattice N) : Prop := selfPairing b v = 0

theorem isSpherical_iff (v : MukaiLattice N) :
    IsSpherical b v ↔ selfPairing b v = -2 := Iff.rfl

theorem isIsotropic_iff (v : MukaiLattice N) :
    IsIsotropic b v ↔ selfPairing b v = 0 := Iff.rfl

theorem IsSpherical.neg {v : MukaiLattice N} (h : IsSpherical b v) :
    IsSpherical b (-v) := by
  rw [IsSpherical, selfPairing_neg]; exact h

theorem IsIsotropic.neg {v : MukaiLattice N} (h : IsIsotropic b v) :
    IsIsotropic b (-v) := by
  rw [IsIsotropic, selfPairing_neg]; exact h

theorem not_isSpherical_and_isIsotropic (v : MukaiLattice N) :
    ¬(IsSpherical b v ∧ IsIsotropic b v) := by
  rintro ⟨hs, hi⟩
  rw [IsSpherical, hi] at hs
  exact absurd hs (by decide)

/-- The numerical quantity `⟪v, v⟫ + 2`.

**A definition, not the Mukai dimension theorem.** See the module docstring. -/
def expectedDim (v : MukaiLattice N) : ℤ := selfPairing b v + 2

theorem expectedDim_eq_zero_iff (v : MukaiLattice N) :
    expectedDim b v = 0 ↔ IsSpherical b v := by
  rw [expectedDim, IsSpherical]; omega

theorem expectedDim_eq_two_iff (v : MukaiLattice N) :
    expectedDim b v = 2 ↔ IsIsotropic b v := by
  rw [expectedDim, IsIsotropic]; omega

/-! ### The hyperbolic plane in the rank / co-rank coordinates

The two outer summands span a copy of the hyperbolic plane `U`, independently
of `b`. This is the lattice-theoretic content of "the Mukai lattice contains
`H⁰ ⊕ H⁴`". -/

/-- `(1, 0, 0)`. -/
def rankUnit : MukaiLattice N := (1, 0, 0)

/-- `(0, 0, 1)`. -/
def corankUnit : MukaiLattice N := (0, 0, 1)

/-- Not `@[simp]`: `pairing_mk` together with `map_zero` already puts the
left-hand side in normal form, and marking this would fail `simpNF`. It is kept
as a readable statement of the outer-plane pairing. -/
theorem pairing_outer (r s r' s' : ℤ) :
    pairing b ((r, (0 : N), s)) ((r', (0 : N), s')) = -(r * s' + r' * s) := by
  simp [pairing]
  ring

theorem isIsotropic_rankUnit : IsIsotropic b (rankUnit : MukaiLattice N) := by
  simp [IsIsotropic, selfPairing_eq_pairing, rankUnit]

theorem isIsotropic_corankUnit : IsIsotropic b (corankUnit : MukaiLattice N) := by
  simp [IsIsotropic, selfPairing_eq_pairing, corankUnit]

/-- The two isotropic generators pair to `-1`: the outer plane is hyperbolic. -/
theorem pairing_rankUnit_corankUnit :
    pairing b (rankUnit : MukaiLattice N) corankUnit = -1 := by
  simp [rankUnit, corankUnit, pairing]

/-! ### Bundled form

The pairing packaged as a `ℤ`-bilinear map, for downstream use with Mathlib's
bilinear/quadratic-form API. -/

/-- The Mukai pairing as a bundled bilinear map. -/
def pairingBilin : MukaiLattice N →ₗ[ℤ] MukaiLattice N →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (pairing b)
    (pairing_add_left b)
    (fun a v w => by rw [pairing_smul_left]; simp)
    (pairing_add_right b)
    (fun a v w => by rw [pairing_smul_right]; simp)

@[simp]
theorem pairingBilin_apply (v w : MukaiLattice N) :
    pairingBilin b v w = pairing b v w :=
  rfl

end Mukai
