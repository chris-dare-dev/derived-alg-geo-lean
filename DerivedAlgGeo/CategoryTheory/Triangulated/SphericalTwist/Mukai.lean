/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.GrothendieckGroup
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.Reflection

/-!
# The `K₀` twist is the Mukai reflection

`LinearAlgebra/Lattice/Mukai/Reflection.lean` says in its own docstring that the
eventual reason it exists is the identity `T_E ↦ ρ_{v(E)}`. This file proves the
`K₀` half of that identity: transported along a Mukai realization
`v : K₀ C →+ MukaiLattice N`, the twist `τ_E` of
`SphericalTwist/GrothendieckGroup.lean` **is** the reflection
`ρ_{v[E]}` of `Reflection.lean`,

```
v (τ_E x) = ρ_{v[E]} (v x).
```

No geometry, no tensor product, no functor, and no sphericity predicate is
involved. The autoequivalence `T_E` still does not exist anywhere in this
repository; what is identified here are two maps of abelian groups.

## `MukaiRealization` is supplied, not proved

Nothing in this file, and nothing in this repository, constructs a
`MukaiRealization`. Its third field is Mukai's theorem — Hirzebruch--Riemann--Roch
in the form `χ(E,F) = -⟪v(E), v(F)⟫` — and it is exactly the external input that
`AlgebraicGeometry/Numerical/GrothendieckGroup/MukaiVector.lean` supplies as
`IntegralMukaiData` together with `chi₂_eq_neg_pairing`. The sign convention is
taken from there deliberately, so the two statements are the same statement.

The structure follows the repository's established supplied-data idiom
(`Duality.Serre.DerivedStatement`, `IntegralMukaiData`,
`K3Surface.EulerRealization`): a reader must not take availability of the
structure as evidence that any category has a Mukai realization.

## Where symmetry is spent

`map_twistK₀` needs symmetry of `b` at exactly one point, `Mukai.pairing_comm`,
and the file is written so that point is visible. `τ_E x` subtracts a multiple
of `[E]` weighted by `χ(E, x)` — the Euler form with `E` on the **left** —
whereas `ρ_s w` adds a multiple of `s` weighted by `⟪w, s⟫` — the lattice
pairing with `w` on the left. The two weights agree only after commuting one of
them, and that is the whole content of the hypothesis. This matches
`Reflection.lean`'s own accounting, where symmetry first appears at
`pairing_reflect_reflect` and not before.

`map_twistK₀` carries **no** sphericity hypothesis, matching `Mukai.reflect`,
which is deliberately defined for arbitrary `s`.

## Trap: which form is `-2`

Sphericity of a Mukai vector is `Mukai.selfPairing b v = -2`, that is
`Mukai.IsSpherical`. It is **not** `Mukai.realForm b v = -2`. `realForm` is
deliberately *half* the self-pairing — it is `(1/2 : ℝ) • realBilin b` — so that
`polar (realForm b) = realPairing b` on the nose, correcting for Mathlib's
`polar` being twice the bilinear form. Comparing a self-pairing against
`realForm` yields `-1` where `-2` is meant, and `reflect_reflect` then fails to
close. Everything here stays on the integral `pairing`; the real form belongs to
the wall chart, which this file does not touch.

## Main results

* `MukaiRealization` — the supplied datum `v` together with symmetry of `b` and
  the Mukai/HRR identity.
* `MukaiRealization.isSpherical_of_chi_eq_two` — `χ(E,E) = 2` makes `v [E]`
  spherical in the lattice sense.
* `MukaiRealization.map_twistK₀` — **the identification**, with no hypothesis on
  `E`.
* `MukaiRealization.map_twistK₀Equiv` — the same at the level of the
  automorphisms, and `chiK₀_twistK₀_twistK₀` recovered from
  `Mukai.pairing_reflect_reflect` rather than reproved.
-/

universe w u v

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable (k : Type w) [DivisionRing k] (C : Type u) [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HomFiniteBounded k C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- **A Mukai realization of `K₀ C` in a lattice `MukaiLattice N`.**

Supplied data, in the repository's established idiom, and **not constructed
anywhere**. See the module docstring.

The three fields are independent and do different work:

* `v` is the Mukai vector as an additive map — no compatibility with `χ` is
  asked of it on its own;
* `symm` is symmetry of the underlying bilinear form `b`. It is a property of
  the lattice, not of `v`, and it is what `Mukai.pairing_comm` consumes;
* `chi_eq_neg_pairing` is **the external input**: Mukai's theorem, equivalently
  Hirzebruch--Riemann--Roch in bilinear form. The sign matches
  `AlgebraicGeometry.Numerical.IntegralMukaiData.chi₂_eq_neg_pairing`
  (`χ(E,F) = -⟪v(E), v(F)⟫`) deliberately; a realization built from that datum
  discharges this field on the nose. -/
structure MukaiRealization {N : Type*} [AddCommGroup N]
    (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ) where
  /-- The Mukai vector, as an additive map out of `K₀ C`. -/
  v : K₀ C →+ Mukai.MukaiLattice N
  /-- Symmetry of the underlying bilinear form. -/
  symm : ∀ x y : N, b x y = b y x
  /-- **Mukai's theorem / HRR**: the Euler form is minus the lattice pairing. -/
  chi_eq_neg_pairing : ∀ x y : K₀ C,
    chiK₀ k C x y = -Mukai.pairing b (v x) (v y)

namespace MukaiRealization

variable {k C} {N : Type*} [AddCommGroup N] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ}
  (R : MukaiRealization k C b)

/-- `χ(E, E) = 2` makes the Mukai vector of `E` spherical.

Immediate from `chi_eq_neg_pairing`: `2 = -⟪v[E], v[E]⟫` is `⟪v[E], v[E]⟫ = -2`,
which is `Mukai.IsSpherical` by definition. Note this is a statement about the
*vector*; no sphericity predicate on the object `E` exists or is needed. -/
theorem isSpherical_of_chi_eq_two {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) :
    Mukai.IsSpherical b (R.v (K₀.of C E)) := by
  have h := R.chi_eq_neg_pairing (K₀.of C E) (K₀.of C E)
  rw [hE] at h
  rw [Mukai.isSpherical_iff, Mukai.selfPairing_eq_pairing]
  omega

/-- **The `K₀` twist is the Mukai reflection.**

`v (τ_E x) = ρ_{v[E]} (v x)`, with no hypothesis on `E`: `Mukai.reflect` is
defined for an arbitrary vector, and so is `twistK₀`.

Symmetry of `b` is spent exactly once, at `Mukai.pairing_comm`, to turn the
lattice weight `⟪v x, v[E]⟫` of `reflect` into the Euler weight
`-χ(E, x) = ⟪v[E], v x⟫` of `twistK₀`. See the module docstring. -/
theorem map_twistK₀ (E : C) (x : K₀ C) :
    R.v (twistK₀ k C E x) = Mukai.reflect b (R.v (K₀.of C E)) (R.v x) := by
  rw [twistK₀_apply, map_sub, map_zsmul, Mukai.reflect_apply,
    Mukai.pairing_comm b R.symm (R.v x) (R.v (K₀.of C E)),
    R.chi_eq_neg_pairing (K₀.of C E) x, neg_smul, sub_neg_eq_add]

/-- The twisted vector is spherical exactly when the original one is; a
corollary of `map_twistK₀` and `Mukai.IsSpherical.reflect`, not a new proof. -/
theorem isSpherical_map_twistK₀ {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) {x : K₀ C}
    (hx : Mukai.IsSpherical b (R.v x)) :
    Mukai.IsSpherical b (R.v (twistK₀ k C E x)) := by
  rw [R.map_twistK₀ E x]
  exact Mukai.IsSpherical.reflect b R.symm (R.isSpherical_of_chi_eq_two hE) hx

/-- The isotropic classes are preserved too, by the same route. -/
theorem isIsotropic_map_twistK₀ {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) {x : K₀ C}
    (hx : Mukai.IsIsotropic b (R.v x)) :
    Mukai.IsIsotropic b (R.v (twistK₀ k C E x)) := by
  rw [R.map_twistK₀ E x]
  exact Mukai.IsIsotropic.reflect b R.symm (R.isSpherical_of_chi_eq_two hE) hx

/-- The expected dimension is a twist invariant, from `Mukai.expectedDim_reflect`. -/
theorem expectedDim_map_twistK₀ {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) (x : K₀ C) :
    Mukai.expectedDim b (R.v (twistK₀ k C E x))
      = Mukai.expectedDim b (R.v x) := by
  rw [R.map_twistK₀ E x]
  exact Mukai.expectedDim_reflect b R.symm _ (R.isSpherical_of_chi_eq_two hE) _

/-- The identification at the level of automorphisms: `twistK₀Equiv` composed
with `v` is `v` composed with `Mukai.reflectEquiv`.

Stated pointwise. `reflectEquiv` is a `≃ₗ[ℤ]` and `twistK₀Equiv` is a `≃+`, so
the two sides live in different bundled types and only their underlying
functions can be compared; writing it pointwise is what avoids inserting a
coercion that would have to be unfolded again at every use. -/
theorem map_twistK₀Equiv {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) (x : K₀ C) :
    R.v (twistK₀Equiv k C hE x)
      = Mukai.reflectEquiv b (R.v (K₀.of C E))
          (R.isSpherical_of_chi_eq_two hE) (R.v x) := by
  rw [twistK₀Equiv_apply, Mukai.reflectEquiv_apply, R.map_twistK₀ E x]

include R in
/-- **`τ_E` preserves `χ`, recovered from the lattice side.**

This is `chiK₀_twistK₀_twistK₀` of `SphericalTwist/GrothendieckGroup.lean` again,
obtained here from `Mukai.pairing_reflect_reflect` through the realization
rather than reproved. The point of stating it twice is that the two routes give
the *same* fact: the direct proof spends symmetry of `χ` on `K₀`, this one
spends symmetry of `b` on the lattice, and `chi_eq_neg_pairing` is what makes
those the same hypothesis. -/
theorem chiK₀_twistK₀_twistK₀ {E : C}
    (hE : chiK₀ k C (K₀.of C E) (K₀.of C E) = 2) (x y : K₀ C) :
    chiK₀ k C (twistK₀ k C E x) (twistK₀ k C E y) = chiK₀ k C x y := by
  rw [R.chi_eq_neg_pairing, R.chi_eq_neg_pairing, R.map_twistK₀ E x,
    R.map_twistK₀ E y,
    Mukai.pairing_reflect_reflect b R.symm _ (R.isSpherical_of_chi_eq_two hE)]

include R in
/-- The Euler form is symmetric on the image of a realization, since the lattice
pairing is. Recorded because `chiK₀_twistK₀_twistK₀` in
`SphericalTwist/GrothendieckGroup.lean` takes symmetry of `χ` as a hypothesis,
and this is what discharges it for a realized category. -/
theorem chiK₀_comm (x y : K₀ C) : chiK₀ k C x y = chiK₀ k C y x := by
  rw [R.chi_eq_neg_pairing, R.chi_eq_neg_pairing,
    Mukai.pairing_comm b R.symm (R.v x) (R.v y)]

end MukaiRealization

end CategoryTheory.Triangulated.SphericalTwist
