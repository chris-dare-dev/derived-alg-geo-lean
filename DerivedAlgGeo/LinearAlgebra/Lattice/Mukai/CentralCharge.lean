/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.RealForm
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.CentralCharge

/-!
# `Z(β,ω)` on the Mukai extension

The central charge of the exponential pair, written out. For `v = (r, c, s)`:

```
Z (r, c, s) = (b β c - s - r * (b β β - b ω ω) / 2) + i * (b ω c - r * b β ω)
```

which is Bridgeland's `Z(β,ω)` — his `⟪exp(β + iω), v⟫`, with the pairing read
on the real and imaginary parts rather than on a complexified space.

The support property comes with it: the classes of vanishing charge are exactly
the orthogonal complement of the plane, where the form is negative definite. On
the Mukai extension that is the statement that the walls are cut out by the
vanishing of `Z`.

`V` is an arbitrary real bilinear space; no geometry is asserted, and `v(E)` for
an object `E` is not defined here.
-/

open QuadraticMap

namespace Mukai

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V)

/-- **`Z(β,ω)`**: the central charge of the exponential pair. -/
noncomputable def expCharge (v : RealExtension V) : ℂ :=
  PeriodDomain.centralCharge (realForm b) (expRe b β ω) (expIm b β ω) v

/-- **`Z(β,ω)` as an additive homomorphism.**

The exponential charge is linear in the Mukai class.  Exposing that structure
at the numerical layer lets categorical consumers compose class maps with the
charge instead of rebuilding its additivity object by object. -/
noncomputable def expChargeHom : RealExtension V →+ ℂ where
  toFun := expCharge b β ω
  map_zero' := by
    simp [expCharge, PeriodDomain.centralCharge]
  map_add' v w := by
    simp only [expCharge, PeriodDomain.centralCharge, polar_add_right]
    push_cast
    ring

@[simp]
theorem expChargeHom_apply (v : RealExtension V) :
    expChargeHom b β ω v = expCharge b β ω v := rfl

/-- **`Z(β,ω)` as an `ℝ`-linear map.**

The additive homomorphism above is enough for the wall arithmetic, but the
support property of
`Triangulated/StabilityCondition/Weak/Support/Predicate/Quadratic.lean` is
stated for an `ℝ`-linear charge, because its quadratic form is.  Real
homogeneity comes from `PeriodDomain.centralCharge_smul`; nothing new is
computed. -/
noncomputable def expChargeLinearMap : RealExtension V →ₗ[ℝ] ℂ where
  toFun := expCharge b β ω
  map_add' := (expChargeHom b β ω).map_add
  map_smul' a v := by
    show expCharge b β ω (a • v) = (a : ℝ) • expCharge b β ω v
    rw [expCharge, expCharge, PeriodDomain.centralCharge_smul, Complex.real_smul]

@[simp]
theorem expChargeLinearMap_apply (v : RealExtension V) :
    expChargeLinearMap b β ω v = expCharge b β ω v := rfl

/-- The charge written out on a triple. This is Bridgeland's formula. -/
theorem expCharge_apply (hb : ∀ x y : V, b x y = b y x) (r : ℝ) (c : V) (s : ℝ) :
    expCharge b β ω (r, c, s)
      = Complex.ofReal (b β c - s - r * (b β β - b ω ω) / 2)
        + Complex.ofReal (b ω c - r * b β ω) * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp [expCharge, PeriodDomain.centralCharge, polar_realForm b hb, realPairing, expRe, expIm]
    ring
  · simp [expCharge, PeriodDomain.centralCharge, polar_realForm b hb, realPairing, expRe, expIm]

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- **The support property for `Z(β,ω)`**: a nonzero class of vanishing charge has
negative square. -/
theorem neg_of_expCharge_eq_zero
    (hsig : PeriodDomain.HasSignatureTwo (realForm b)) (hb : ∀ x y : V, b x y = b y x)
    (hω : 0 < b ω ω) {v : RealExtension V} (hv : expCharge b β ω v = 0) (hv0 : v ≠ 0) :
    realForm b v < 0 :=
  PeriodDomain.neg_of_centralCharge_eq_zero hsig (isPositivePair_exp b β ω hb hω) hv hv0

/-- **No class of nonnegative square is killed by `Z(β,ω)`** — there are no walls
in the positive cone. -/
theorem expCharge_ne_zero_of_nonneg
    (hsig : PeriodDomain.HasSignatureTwo (realForm b)) (hb : ∀ x y : V, b x y = b y x)
    (hω : 0 < b ω ω) {v : RealExtension V} (hv : 0 ≤ realForm b v) (hv0 : v ≠ 0) :
    expCharge b β ω v ≠ 0 :=
  PeriodDomain.centralCharge_ne_zero_of_nonneg hsig (isPositivePair_exp b β ω hb hω) hv hv0

omit [FiniteDimensional ℝ V] in
/-- **A spherical wall is a vanishing charge.** -/
theorem mem_wall_iff_expCharge_eq_zero (hb : ∀ x y : V, b x y = b y x) (hω : 0 < b ω ω)
    {δ : RealExtension V} :
    PeriodDomain.pairSpan (expRe b β ω) (expIm b β ω) ∈ PeriodDomain.wall (realForm b) δ ↔
      expCharge b β ω δ = 0 :=
  PeriodDomain.mem_wall_iff_centralCharge_eq_zero (isPositivePair_exp b β ω hb hω)

omit [FiniteDimensional ℝ V] in
/-- **`P₀` for the exponential pair is where `Z(β,ω)` kills nothing in `Δ`.**
With `Δ` the spherical classes of the Mukai lattice this is Bridgeland's cut
period domain. -/
theorem mem_periodDomain₀_iff_expCharge_ne_zero (hb : ∀ x y : V, b x y = b y x)
    (hω : 0 < b ω ω) (Δ : Set (RealExtension V)) :
    PeriodDomain.pairSpan (expRe b β ω) (expIm b β ω) ∈
        PeriodDomain.periodDomain₀ (realForm b) Δ ↔
      ∀ δ ∈ Δ, expCharge b β ω δ ≠ 0 :=
  PeriodDomain.mem_periodDomain₀_iff_centralCharge_ne_zero
    (isPositivePair_exp b β ω hb hω) Δ

end FiniteDimensional

end Mukai

namespace Mukai

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V)

/-! The elementary charge identities are projections of `expChargeHom`. -/

/-- The exponential charge kills the zero class. -/
@[simp]
theorem expCharge_zero : Mukai.expCharge b β ω 0 = 0 :=
  (expChargeHom b β ω).map_zero

/-- The exponential charge is additive in the Mukai class. -/
theorem expCharge_add (v w : Mukai.RealExtension V) :
    Mukai.expCharge b β ω (v + w) =
      Mukai.expCharge b β ω v + Mukai.expCharge b β ω w :=
  (expChargeHom b β ω).map_add v w

/-- The exponential charge negates on negated classes. -/
theorem expCharge_neg (v : Mukai.RealExtension V) :
    Mukai.expCharge b β ω (-v) = -Mukai.expCharge b β ω v :=
  (expChargeHom b β ω).map_neg v

end Mukai
