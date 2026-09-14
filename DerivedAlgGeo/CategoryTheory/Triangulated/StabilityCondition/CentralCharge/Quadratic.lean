/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.CentralCharge
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.OrthogonalityLocus
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PositiveFrame

/-!
# Quadratic-space interpretations of paired complex functionals

`LinearAlgebra/QuadraticForm/ComplexPairing.lean` owns the functional and its
kernel algebra. This file is the downstream adapter that interprets kernel
vanishing against the orthogonality loci attached to positive frames.

Kernel negativity alone is not called the quadratic support property here.
The full predicate in `Weak/Support/Predicate/Quadratic.lean` also requires the
same quadratic form to be nonnegative on the selected semistable classes.
No determinant alignment or destabilization claim is made here.
-/

open QuadraticMap

namespace PeriodDomain

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}

/-- A class is orthogonal to the plane underlying a positive frame exactly when its paired complex
functional vanishes. -/
theorem mem_orthogonalityLocus_iff_centralCharge_eq_zero {x y : M}
    (hxy : IsPositiveFrame Q x y) {δ : M} :
    framePlane (x, y) ∈ orthogonalityLocus Q δ ↔ centralCharge Q x y δ = 0 := by
  rw [mem_orthogonalityLocus_iff_mem_orthogonal hxy, framePlane_mk, centralCharge_eq_zero_iff]

/-- A positive frame maps into the deleted-locus complement exactly when its paired complex
functional kills no member of the cutting set. -/
theorem mem_positivePlanesAway_iff_centralCharge_ne_zero {x y : M} (hxy : IsPositiveFrame Q x y)
    (Δ : Set M) :
    framePlane (x, y) ∈ positivePlanesAway Q Δ ↔ ∀ δ ∈ Δ, centralCharge Q x y δ ≠ 0 := by
  constructor
  · rintro ⟨-, hcut⟩ δ hδ hz
    exact hcut δ hδ ((mem_orthogonalityLocus_iff_centralCharge_eq_zero hxy).mpr hz)
  · intro h
    exact ⟨hxy, fun δ hδ hw =>
      h δ hδ ((mem_orthogonalityLocus_iff_centralCharge_eq_zero hxy).mp hw)⟩

end PeriodDomain

namespace Mukai

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V)

/-- A spherical orthogonality locus for the exponential pair is the vanishing
locus of its additive exponential charge. -/
theorem mem_orthogonalityLocus_iff_expCharge_eq_zero (hb : ∀ x y : V, b x y = b y x)
    (hω : 0 < b ω ω)
    {δ : RealExtension V} :
    PeriodDomain.framePlane (expRe b β ω, expIm b β ω) ∈
      PeriodDomain.orthogonalityLocus (realForm b) δ ↔
      expCharge b β ω δ = 0 :=
  PeriodDomain.mem_orthogonalityLocus_iff_centralCharge_eq_zero (isPositiveFrame_exp b β ω hb hω)

/-- The cut exponential period domain is the locus where the charge kills no
class in `Δ`. -/
theorem mem_positivePlanesAway_iff_expCharge_ne_zero (hb : ∀ x y : V, b x y = b y x)
    (hω : 0 < b ω ω) (Δ : Set (RealExtension V)) :
    PeriodDomain.framePlane (expRe b β ω, expIm b β ω) ∈
        PeriodDomain.positivePlanesAway (realForm b) Δ ↔
      ∀ δ ∈ Δ, expCharge b β ω δ ≠ 0 :=
  PeriodDomain.mem_positivePlanesAway_iff_centralCharge_ne_zero
    (isPositiveFrame_exp b β ω hb hω) Δ

end Mukai
