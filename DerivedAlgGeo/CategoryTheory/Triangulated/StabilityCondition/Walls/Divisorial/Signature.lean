/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.BilinearForm.HodgeIndex
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.OrthogonalityFiniteness

/-!
# Spherical-wall finiteness for exponential planes

The Hodge-index certificate, its signature calculation, and nondegeneracy now
live in the neutral linear-algebra module
`LinearAlgebra/BilinearForm/HodgeIndex.lean`.  This downstream wall module uses
that input to form the exponential positive plane and count lattice classes
whose spherical orthogonality walls pass through it.

No geometric surface or ample cone is constructed here.  `D` is an arbitrary
finite-dimensional real space and the lattice is the integer span of a supplied
real basis.
-/

open QuadraticMap Mukai

universe w

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

namespace DivisorSpace

variable {D : Type w} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {S : DivisorSpace D} {H : D}

/-- The positive plane of `exp(B + iω)`, spanned by its real and imaginary
parts. -/
def expPlane (S : DivisorSpace D) (B omega : D) : Submodule ℝ (Mukai.RealExtension D) :=
  PeriodDomain.pairSpan (Mukai.expRe S.intersection B omega)
    (Mukai.expIm S.intersection B omega)

/-- The exponential plane is positive as soon as `ω² > 0`; the `B`-field is
unconstrained. -/
theorem isPositivePlane_expPlane (S : DivisorSpace D) (B omega : D)
    (homega : 0 < S.pair omega omega) :
    PeriodDomain.IsPositivePlane (Mukai.realForm S.intersection) (expPlane S B omega) :=
  Mukai.isPositiveFrame_exp S.intersection B omega (fun x y => S.pair_comm x y) homega

variable [FiniteDimensional ℝ D]

/-- For a lattice in the real Mukai extension, only finitely many spherical
classes have a wall through the exponential plane. -/
theorem finite_walls_through_expPlane (h : S.HodgeDefinite H) (B omega : D)
    (homega : 0 < S.pair omega omega)
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ (Mukai.RealExtension D)) :
    {δ : Mukai.RealExtension D |
        PeriodDomain.IsSphericalClass (Mukai.realForm S.intersection) δ ∧
        expPlane S B omega ∈ PeriodDomain.orthogonalityLocus (Mukai.realForm S.intersection) δ ∧
        δ ∈ (Submodule.span ℤ (Set.range b) : Set (Mukai.RealExtension D))}.Finite :=
  PeriodDomain.finite_orthogonalityLoci_through (hasSignatureTwo_of_hodgeDefinite h)
    (isPositivePlane_expPlane S B omega homega) b

/-- The same finiteness, stated as a bounded set of spherical classes
orthogonal to the plane. -/
theorem finite_sphericalOrthogonal_expPlane (h : S.HodgeDefinite H) (B omega : D)
    (homega : 0 < S.pair omega omega)
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ (Mukai.RealExtension D)) :
    (PeriodDomain.sphericalOrthogonal (Mukai.realForm S.intersection) (expPlane S B omega)
      ∩ (Submodule.span ℤ (Set.range b) : Set (Mukai.RealExtension D))).Finite :=
  PeriodDomain.finite_sphericalOrthogonal_inter (hasSignatureTwo_of_hodgeDefinite h)
    (isPositivePlane_expPlane S B omega homega) b

end DivisorSpace

end


end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
