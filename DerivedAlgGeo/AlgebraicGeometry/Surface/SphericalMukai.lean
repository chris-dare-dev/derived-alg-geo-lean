/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Surface.Spherical

/-!
# `EulerRealization` from a bilinear Riemann--Roch statement

`Surface/Spherical.lean` crosses from `Dᵇ(Coh X)` to the numerical layer through
`EulerRealization`, a structure with no constructor and no stated provenance: a class map `cls`
together with the identity `χ_num(cls E, cls E) = χ(E, E)` on objects with the spherical Ext
profile. This file gives it one. `BilinearRiemannRochStatement` is the two-variable identity
`χ_num(cls E, cls F) = χ(E, F)`, stated for pairs whose `Hom` is concentrated in degrees `0`--`2`,
and `BilinearRiemannRochStatement.toEulerRealization` restricts it to the diagonal along
spherical objects. The sphericity result then reads "given bilinear HRR" rather than "given this
particular restriction of it to spherical objects".

## Supplied, not proved

In the idiom of `Duality.Serre.DerivedStatement`: `BilinearRiemannRochStatement` carries a
genuinely external input as a field. Proving it is bilinear Hirzebruch--Riemann--Roch, and the
finiteness it presupposes -- that each `Hom(E, F⟦i⟧)` is a finite-dimensional `k`-space, so that
`finrank` measures it -- is the `Hom`-finiteness of `#332`. Nothing here constructs one, and this
file does not attempt HRR.

## Why the amplitude condition is a hypothesis of `chi₂_eq`, and not a field

`euler E F` is a three-term sum over degrees `0, 1, 2`, so the identity `χ_num = euler` can only
be expected where `Hom(E, F⟦i⟧)` vanishes outside that window. A field asserting that vanishing
*for all pairs* would be false, and would make the structure uninhabitable: for any nonzero `E`
and `F := E⟦-5⟧`, the group `E ⟶ F⟦5⟧ = E ⟶ E⟦-5⟧⟦5⟧` contains an isomorphism. Boundedness of
`Dᵇ(Coh X)` gives a per-object amplitude, never a uniform bound across pairs; the honest bound
`Extⁱ(E, F) = 0` outside `0..2` holds for pairs of objects of the heart, not for arbitrary
complexes. So the condition is where it is true: a hypothesis of `chi₂_eq`, per pair. A spherical
`E` satisfies it for the pair `(E, E)` by its own `vanishing` field, which is what makes the
restriction to `EulerRealization` go through.

## No `cls_iso` field

Nothing in this file consumes invariance of `cls` under isomorphism, and `MukaiVector.lean`
records the precedent: a field whose measured use count is zero is a field that should not exist.

## What is still missing

Two facts a witness needs and does not have:

* **finite-dimensionality of `Hom` in `Dᵇ(Coh X)`** (`#332`). The Serre-finiteness chain now
  proves `Hⁱ(X, F)` finite-dimensional for every coherent `F` on a projective variety
  (`Cohomology/Finiteness/ProjectiveVariety.lean`); the passage from sheaf cohomology to
  `Hom(E, F⟦i⟧)` in the derived category is not in the tree.
* **the Hirzebruch--Riemann--Roch identity itself**, which is what the `chi₂_eq` field asserts.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

namespace K3Surface

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k X]

/-- `χ(E, F)` in the three degrees `0, 1, 2`: the two-variable form of `selfEuler`.

A definition for every pair, but only the intended invariant for a pair whose `Hom`-groups vanish
outside `0, 1, 2`; `finrank` is `0` on a group of infinite dimension, so the value is never junk,
only uninformative. `selfEuler E` is `euler E E` on the nose. -/
noncomputable def euler (E F : DerivedCat X) : ℤ :=
  (Module.finrank k (E ⟶ F) : ℤ)
    - (Module.finrank k (E ⟶ F⟦(1 : ℤ)⟧) : ℤ)
    + (Module.finrank k (E ⟶ F⟦(2 : ℤ)⟧) : ℤ)

/-- `selfEuler` is the diagonal of `euler`, definitionally. -/
theorem selfEuler_eq_euler_self (E : DerivedCat X) : selfEuler E = euler E E := rfl

variable (k) in
/-- **Bilinear Hirzebruch--Riemann--Roch, as a supplied statement.**

The numerical Euler pairing computes the alternating sum of `Hom`-dimensions in `Dᵇ(Coh X)`, for
pairs whose `Hom` is concentrated in degrees `0`--`2`. That amplitude condition is a hypothesis of
`chi₂_eq` and deliberately not a field: as a field it would be false, see the module docstring.

Supplied, not proved. Proving it is bilinear HRR, and the finiteness it presupposes is `#332`. -/
structure BilinearRiemannRochStatement {A : Type*} {N : Type*} [CommRing A] [Algebra ℚ A]
    [AddCommGroup N] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [IsSmoothProperVariety k X] (V : Numerical.NumericalVarietyData 2 A N) where
  /-- The class of an object in the numerical Grothendieck group. -/
  cls : DerivedCat X → N
  /-- The two Euler pairings agree on pairs concentrated in degrees `0`--`2`. -/
  chi₂_eq : ∀ E F : DerivedCat X,
    (∀ i : ℤ, i ≠ 0 → i ≠ 1 → i ≠ 2 → ∀ f : E ⟶ F⟦i⟧, f = 0) →
    V.chi₂ (cls E) (cls F) = (euler E F : ℚ)

namespace BilinearRiemannRochStatement

variable {A : Type*} {N : Type*} [CommRing A] [Algebra ℚ A] [AddCommGroup N]
  {V : Numerical.NumericalVarietyData 2 A N}

/-- **Bilinear HRR restricts to an `EulerRealization`.** The class map transports unchanged; the
diagonal identity for a spherical `E` is `chi₂_eq` at `(E, E)`, whose amplitude hypothesis is the
profile's own `vanishing`. -/
noncomputable def toEulerRealization (S : BilinearRiemannRochStatement k X V) :
    EulerRealization k X V where
  cls := S.cls
  chi₂_eq E h := by
    rw [selfEuler_eq_euler_self]
    exact S.chi₂_eq E E fun i h₀ _ h₂ => h.vanishing i h₀ h₂

end BilinearRiemannRochStatement

/-- **An object with the profile has a spherical Mukai vector, given bilinear HRR.**
`SphericalExtProfile.isSpherical_mukaiVector` against the realization that
`BilinearRiemannRochStatement.toEulerRealization` produces. -/
theorem SphericalExtProfile.isSpherical_mukaiVector_of_statement {A : Type*} {N : Type*}
    {Λ : Type*} [CommRing A] [Algebra ℚ A] [AddCommGroup N] [AddCommGroup Λ]
    {V : Numerical.NumericalVarietyData 2 A N} (S : BilinearRiemannRochStatement k X V)
    (D : Numerical.K3.IntegralMukaiData V Λ) (hHRR : V.SatisfiesHRR)
    (hK3 : Numerical.K3.IsK3 V) {E : DerivedCat X} (h : SphericalExtProfile E) :
    Mukai.IsSpherical D.b (D.mukaiVector (S.cls E)) :=
  h.isSpherical_mukaiVector S.toEulerRealization D hHRR hK3

end K3Surface

end AlgebraicGeometry
