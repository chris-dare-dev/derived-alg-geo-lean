/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Core numerical data of a smooth projective variety over a field

This is **Layer A** of `DerivedAlgGeo`: the numerical interface that Bridgeland-stability
arguments actually consume from a smooth projective variety, stated for a variety of
*arbitrary* dimension `n` so that the surface case (`n = 2`), the threefold case
(`n = 3`) and the fourfold case (`n = 4`) are specialisations rather than rewrites.

## Design

Two explicit data bundles:

* `NumericalRingData n A` — `A` is the numerical intersection ring `A^•(X)_ℚ`: a commutative
  `ℚ`-algebra graded by codimension, concentrated in degrees `0, …, n`, with a `ℚ`-linear
  degree map `∫_X : A → ℚ` supported in top codimension.
* `NumericalVarietyData n A N` — adds the numerical Grothendieck group `N`, the Chern
  character, the Todd class of `X` and the Euler characteristic.

These bundles are passed explicitly: a carrier may support more than one numerical
presentation. Hirzebruch--Riemann--Roch is the separate proposition-valued property
`NumericalVarietyData.SatisfiesHRR`.

## Trust boundary

`NumericalVarietyData` records a selected presentation and its structural compatibility
laws; it does not assert that the presentation comes from geometry. In particular HRR is
not a field. Proving `SatisfiesHRR` is the job of Layer B
(`DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent`), which builds `Coh X`, sheaf cohomology,
`χ`, and intersection numbers from Mathlib's scheme theory. Any downstream result that uses
HRR must receive that witness explicitly.

Graded components of `ch` and `td` are carried as **data** (`chComp`, `toddComp`) rather
than extracted by a projection operator. That is deliberate: it keeps this file free of
graded-decomposition machinery, and every consumer needs the components anyway.

## References

* Hirzebruch, *Topological Methods in Algebraic Geometry*, §21
* Fulton, *Intersection Theory*, ch. 15 and 18
* Huybrechts–Lehn, *The Geometry of Moduli Spaces of Sheaves*, §1.1 and §2.1
-/

universe u v

namespace AlgebraicGeometry.Numerical

/-- A **numerical intersection ring of dimension `n`**: a commutative `ℚ`-algebra `A`
graded by codimension and concentrated in degrees `0, …, n`, together with a `ℚ`-linear
degree map `degree` (written `∫_X` in the literature) supported in top codimension.

The bundle is explicit because the same carrier can support several numerical
presentations (for example, different degree normalizations). -/
structure NumericalRingData (n : ℕ) (A : Type u) [CommRing A] [Algebra ℚ A] where
  /-- The codimension-`i` graded piece `Aⁱ`. -/
  piece : ℕ → Submodule ℚ A
  /-- The pieces decompose `A`, i.e. `A = ⨁ᵢ Aⁱ`. -/
  isInternal : DirectSum.IsInternal piece
  /-- Nothing lives above the dimension: `Aⁱ = 0` for `i > n`. -/
  piece_eq_bot_of_lt : ∀ ⦃i : ℕ⦄, n < i → piece i = ⊥
  /-- `1 ∈ A⁰`. -/
  one_mem_piece_zero : (1 : A) ∈ piece 0
  /-- The grading is multiplicative: `Aⁱ · Aʲ ⊆ Aⁱ⁺ʲ`. -/
  mul_mem_piece : ∀ {i j : ℕ} {x y : A}, x ∈ piece i → y ∈ piece j → x * y ∈ piece (i + j)
  /-- The degree map `∫_X : A → ℚ`. -/
  degree : A →ₗ[ℚ] ℚ
  /-- `∫_X` kills every graded piece other than the top one. -/
  degree_eq_zero_of_mem : ∀ {i : ℕ} {x : A}, i ≠ n → x ∈ piece i → degree x = 0

namespace NumericalRingData

variable {n : ℕ} {A : Type u} [CommRing A] [Algebra ℚ A]

/-- Scalars sit in codimension zero. -/
theorem algebraMap_mem_piece_zero (R : NumericalRingData n A) (q : ℚ) :
    algebraMap ℚ A q ∈ R.piece 0 := by
  have h : algebraMap ℚ A q = q • (1 : A) := by
    rw [Algebra.smul_def, mul_one]
  rw [h]
  exact Submodule.smul_mem _ _ R.one_mem_piece_zero

/-- `∫_X` is `ℚ`-homogeneous in the sense we actually use it: pulling a scalar out of a
product with `algebraMap`. -/
theorem degree_algebraMap_mul (R : NumericalRingData n A) (q : ℚ) (x : A) :
    R.degree (algebraMap ℚ A q * x) = q * R.degree x := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- Anything in a piece above the dimension is zero. -/
theorem eq_zero_of_mem_piece_of_lt (R : NumericalRingData n A)
    {i : ℕ} (hi : n < i) {x : A} (hx : x ∈ R.piece i) :
    x = 0 := by
  rw [R.piece_eq_bot_of_lt hi] at hx
  simpa using hx

end NumericalRingData

/-- **Numerical data of a smooth projective variety of dimension `n` over a field.**

`A` is the numerical intersection ring `A^•(X)_ℚ` and `N` is the numerical Grothendieck
group `N(X) = K(X)/≡`. The Chern character is carried by its graded components
`chComp E i = chᵢ(E)`, the Todd class of `X` by `toddComp i = tdᵢ(X)`.

Hirzebruch--Riemann--Roch is deliberately kept outside this data bundle as
`NumericalVarietyData.SatisfiesHRR`. -/
structure NumericalVarietyData (n : ℕ) (A : Type u) (N : Type v)
    [CommRing A] [Algebra ℚ A] [AddCommGroup N] where
  /-- The selected numerical intersection-ring presentation. -/
  ring : NumericalRingData n A
  /-- The rank homomorphism `N(X) → ℤ`. -/
  rank : N →+ ℤ
  /-- The codimension-`i` component of the Chern character, `chᵢ(E)`. -/
  chComp : N → ℕ → A
  /-- `chᵢ(E)` lives in codimension `i`. -/
  chComp_mem : ∀ (E : N) (i : ℕ), chComp E i ∈ ring.piece i
  /-- `ch₀(E) = rank E`. -/
  chComp_zero : ∀ E : N, chComp E 0 = algebraMap ℚ A (rank E : ℚ)
  /-- The Chern character is additive on `N(X)`. -/
  chComp_add : ∀ (E F : N) (i : ℕ), chComp (E + F) i = chComp E i + chComp F i
  /-- The codimension-`i` component of the Todd class of `X`. -/
  toddComp : ℕ → A
  /-- `tdᵢ(X)` lives in codimension `i`. -/
  toddComp_mem : ∀ i : ℕ, toddComp i ∈ ring.piece i
  /-- `td₀(X) = 1`. -/
  toddComp_zero : toddComp 0 = (1 : A)
  /-- The Euler characteristic `χ(E) = Σᵢ (-1)ⁱ dim Hⁱ(X, E)`. -/
  chi : N →+ ℤ

namespace NumericalVarietyData

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]


/-- Hirzebruch--Riemann--Roch as a proposition-valued property of one explicit
numerical presentation. It is not selected by typeclass inference. -/
structure SatisfiesHRR (V : NumericalVarietyData n A N) : Prop where
  /-- `χ(E) = ∫_X ch(E) · td(X)`. -/
  eq : ∀ E : N, (V.chi E : ℚ) = V.ring.degree
    ((∑ i ∈ Finset.range (n + 1), V.chComp E i) *
      (∑ j ∈ Finset.range (n + 1), V.toddComp j))

/-- The Chern character `ch(E) = Σᵢ chᵢ(E)`. -/
def ch (V : NumericalVarietyData n A N) (E : N) : A :=
  ∑ i ∈ Finset.range (n + 1), V.chComp E i

/-- The Todd class `td(X) = Σᵢ tdᵢ(X)`. -/
def todd (V : NumericalVarietyData n A N) : A :=
  ∑ j ∈ Finset.range (n + 1), V.toddComp j

/-- Hirzebruch–Riemann–Roch, restated in terms of `ch` and `todd`. -/
theorem hrr (V : NumericalVarietyData n A N) (hV : V.SatisfiesHRR) (E : N) :
    (V.chi E : ℚ) = V.ring.degree (V.ch E * V.todd) :=
  hV.eq E

/-- Components of the Chern character above the dimension vanish. -/
theorem chComp_eq_zero_of_lt (V : NumericalVarietyData n A N)
    (E : N) {i : ℕ} (hi : n < i) : V.chComp E i = 0 :=
  V.ring.eq_zero_of_mem_piece_of_lt hi (V.chComp_mem E i)

/-- Components of the Todd class above the dimension vanish. -/
theorem toddComp_eq_zero_of_lt (V : NumericalVarietyData n A N)
    {i : ℕ} (hi : n < i) : V.toddComp i = 0 :=
  V.ring.eq_zero_of_mem_piece_of_lt hi (V.toddComp_mem i)

/-- The degree of a mixed term `chᵢ(E) · tdⱼ(X)` vanishes unless `i + j = n`.

This is the single computational fact behind every dimension-specific Riemann–Roch
formula: expanding `ch(E) · td(X)` leaves only the terms of total codimension `n`. -/
theorem degree_chComp_mul_toddComp_eq_zero (V : NumericalVarietyData n A N)
    (E : N) {i j : ℕ} (hij : i + j ≠ n) :
    V.ring.degree (V.chComp E i * V.toddComp j) = 0 :=
  V.ring.degree_eq_zero_of_mem hij
    (V.ring.mul_mem_piece (V.chComp_mem E i) (V.toddComp_mem j))

end NumericalVarietyData

end AlgebraicGeometry.Numerical
