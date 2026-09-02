/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Linear
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.MukaiVector
import DerivedAlgGeo.AlgebraicGeometry.Surface.K3

/-!
# Spherical objects on a K3 surface

An object `E` of `Dᵇ(Coh X)` is **spherical** when its graded self-`Hom` algebra
is that of a two-sphere:

```
Hom(E, E⟦i⟧) ≅ k   for i = 0 and i = 2,      and 0 otherwise.
```

That is Huybrechts, *Fourier--Mukai Transforms in Algebraic Geometry*,
Definition 8.1, specialised to a K3.

## Why the definition is this short here

Huybrechts' Definition 8.1 has two clauses. The first, `E ⊗ ω_X ≅ E`, is
**automatic on a K3**: `IsK3Surface.canonicalClass_eq_one` says `ω_X` is trivial
in `Pic X`, so tensoring by it is the identity up to isomorphism. Dropping that
clause is the whole reason this file needs no derived tensor product, and it is
why the K3 case is reachable while the general smooth projective case is not.
For `dim X = n` in general the first clause is a genuine hypothesis and its
formalization waits on `⊗ᴸ`.

## Why it is expressible at all

`Hom(E, E⟦i⟧) ≅ k` is not a statement about an abelian group. Until
`CoherentSheaf/Linear.lean` constructed the `k`-linear structure on `Coh X` — and
Mathlib carried it to `Dᵇ(Coh X)` — the right-hand side had no meaning here, and
`Numerical/GrothendieckGroup/MukaiVector.lean` said as much in its docstring:
sphericity of an *object* needs an `Ext` that layer does not have. This file is
that docstring's target.

## What is a hypothesis, and what that costs

`end_one` and `ext_two` are **fields, not theorems**. Nothing here proves that
any particular object has one-dimensional endomorphisms; finite-dimensionality
of `Hom` in `Dᵇ(Coh X)` is not available (issue #332, behind the S1--S4
Serre-finiteness chain), so a `Hom`-group is a `k`-vector space of unknown
dimension until someone supplies otherwise.

The consequence is worth stating plainly: this file **defines** sphericity and
proves the handful of things that follow from the definition alone. It does not
exhibit a spherical object, and it cannot, because exhibiting one means
computing a `Hom`-group.

## What is deliberately absent

* **No spherical twist.** `T_E` needs the evaluation triangle and a functorial
  cone; cones are not functorial in a triangulated category. See the scope notes
  on the dg-enhancement route (issue #378).
* **No Serre duality.** On a K3, `Hom(E, E⟦2⟧) ≅ Hom(E, E)ᵛ` would make
  `ext_two` follow from `end_one`, which is exactly how the literature states
  sphericity as "simple and rigid". `Duality/Serre/` carries duality as
  realization data, not as a theorem, so the two clauses stay independent here.

## Main results

* `IsSphericalObject` — the definition.
* `IsSphericalObject.not_isZero` — a spherical object is nonzero. The one thing
  that follows from `end_one` with no further input, and the reason the
  definition is not vacuous on the zero object.
* `IsSphericalObject.finrank_end` — `dimₖ End(E) = 1`.
* `IsSphericalObject.of_iso` — sphericity is invariant under isomorphism.
* `IsSphericalObject.selfEuler_eq_two` — `χ(E,E) = 1 - 0 + 1 = 2`, computed
  from the definition rather than assumed.
* `IsSphericalObject.isSpherical_mukaiVector` — a spherical object has a
  spherical Mukai vector, given an `EulerRealization`.

## A trap worth recording

The vanishing clause says `∀ f : E ⟶ E⟦i⟧, f = 0`, and **not**
`IsZero (E ⟶ E⟦i⟧)`. The second is well-typed and always false: `E ⟶ E⟦i⟧` is a
bare `Type`, `IsZero` there asks for an object that is both initial and
terminal, and `Type` has none — `Empty` and `PUnit` are different. Writing it
that way compiles and makes the whole structure uninhabitable, so every theorem
about spherical objects becomes vacuously true.

`IsK3Surface.h1_vanishing` *does* use `IsZero`, correctly, because
`Cohomology.coherentH` lands in `AddCommGrpCat`, which has a zero object. The
difference is the target category, not the mathematics.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.DerivedCategory

namespace AlgebraicGeometry

namespace K3Surface

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k X]

/-- The bounded derived category of coherent sheaves on a K3 surface.

An abbreviation for readability only; everything about it comes from
`AlgebraicGeometry.DerivedCategory.SchemeBoundedCoherentDerivedCategory`. -/
abbrev DerivedCat : Type _ := SchemeBoundedCoherentDerivedCategory X

variable {X}

/-- **A spherical object on a K3 surface.**

Huybrechts' Definition 8.1 with its first clause discharged by triviality of
`ω_X`; see the module docstring. `end_one` and `ext_two` are hypotheses, and
what that costs is also in the module docstring. -/
structure IsSphericalObject (E : DerivedCat X) : Prop where
  /-- `Hom(E, E⟦i⟧) = 0` away from degrees `0` and `2`. Stated as "every
  morphism is zero" rather than `IsZero`; see the trap in the module
  docstring. -/
  vanishing : ∀ i : ℤ, i ≠ 0 → i ≠ 2 → ∀ f : E ⟶ E⟦i⟧, f = 0
  /-- `End(E) ≅ k`: the object is simple. Existence of an isomorphism, so that
  sphericity is a property and not a choice of one. -/
  end_one : Nonempty ((E ⟶ E) ≃ₗ[k] k)
  /-- `Hom(E, E⟦2⟧) ≅ k`. On a K3 this is Serre-dual to `end_one`, but duality
  is realization data here, so it is asked for separately. -/
  ext_two : Nonempty ((E ⟶ E⟦(2 : ℤ)⟧) ≃ₗ[k] k)

namespace IsSphericalObject

variable {E F : DerivedCat X} (h : IsSphericalObject (k := k) E)

include h

/-- **A spherical object is nonzero.**

If `E` were a zero object its endomorphism group would be a subsingleton, and
`end_one` would make `k` one too — impossible for a field. This is the only
consequence of `end_one` that needs no finiteness input, and it is what stops
the definition being satisfied vacuously. -/
theorem not_isZero : ¬ IsZero E := by
  intro hE
  have hsub : Subsingleton (E ⟶ E) := ⟨fun f g => hE.eq_of_src f g⟩
  have : Subsingleton k := h.end_one.some.toEquiv.symm.subsingleton
  exact (not_subsingleton k) this

/-- The endomorphism algebra of a spherical object is one-dimensional. -/
theorem finrank_end : Module.finrank k (E ⟶ E) = 1 := by
  rw [h.end_one.some.finrank_eq, Module.finrank_self]

/-- `Hom(E, E⟦2⟧)` is one-dimensional. -/
theorem finrank_ext_two : Module.finrank k (E ⟶ E⟦(2 : ℤ)⟧) = 1 := by
  rw [h.ext_two.some.finrank_eq, Module.finrank_self]

/-- **Sphericity is invariant under isomorphism.**

Transport along `Linear.homCongr`, which is the `k`-linear isomorphism of
`Hom`-groups induced by isomorphisms of source and target; the target side is
the isomorphism shifted. -/
theorem of_iso (e : E ≅ F) : IsSphericalObject (k := k) F where
  vanishing i hi₀ hi₂ f := by
    have hz := h.vanishing i hi₀ hi₂
      ((Linear.homCongr k e ((shiftFunctor (DerivedCat X) i).mapIso e)).symm f)
    have := congrArg (Linear.homCongr k e ((shiftFunctor (DerivedCat X) i).mapIso e)) hz
    simpa using this
  end_one := ⟨(Linear.homCongr k e.symm e.symm).trans h.end_one.some⟩
  ext_two :=
    ⟨(Linear.homCongr k e.symm
      ((shiftFunctor (DerivedCat X) (2 : ℤ)).mapIso e.symm)).trans h.ext_two.some⟩

/-! ### The numerical shadow

Sphericity of an object forces its self-Euler characteristic to be `2`, which is
exactly the numerical condition `Numerical.K3.isSpherical_mukaiVector_iff`
characterises. Computing it needs nothing beyond the definition: the alternating
sum has three terms, and sphericity gives all three.

**Only the forward direction.** `MukaiVector.lean` is explicit that recovering
sphericity of an *object* from `χ(E,E) = 2` needs simplicity and Serre duality;
that converse is not attempted here and is not available. What follows is the
easy direction, and it is the one that connects this file to the lattice theory
in `LinearAlgebra/Lattice/Mukai/`. -/

/-- Degrees other than `0` and `2` contribute nothing. -/
theorem finrank_hom_eq_zero (i : ℤ) (hi₀ : i ≠ 0) (hi₂ : i ≠ 2) :
    Module.finrank k (E ⟶ E⟦i⟧) = 0 := by
  have : Subsingleton (E ⟶ E⟦i⟧) :=
    ⟨fun f g => by rw [h.vanishing i hi₀ hi₂ f, h.vanishing i hi₀ hi₂ g]⟩
  exact Module.finrank_zero_of_subsingleton

end IsSphericalObject

/-- `χ(E, E)` in the only three degrees where `Hom` can be nonzero.

A definition for every object, but only the intended invariant for one whose
`Hom`-groups vanish outside `0, 1, 2` — which on a K3 is what sphericity
supplies. It is not claimed to agree with any numerical Euler pairing; that
comparison is `EulerRealization`. -/
noncomputable def selfEuler {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [IsSmoothProperVariety k X] (E : DerivedCat X) : ℤ :=
  (Module.finrank k (E ⟶ E) : ℤ)
    - (Module.finrank k (E ⟶ E⟦(1 : ℤ)⟧) : ℤ)
    + (Module.finrank k (E ⟶ E⟦(2 : ℤ)⟧) : ℤ)

namespace IsSphericalObject

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X]
  {E : DerivedCat X} (h : IsSphericalObject E)

include h

/-- **A spherical object has self-Euler characteristic `2`.**

`1 - 0 + 1`. Every term comes from the definition: the outer two from `end_one`
and `ext_two`, the middle from `vanishing`. -/
theorem selfEuler_eq_two : selfEuler E = 2 := by
  rw [selfEuler, h.finrank_end, h.finrank_ext_two,
    h.finrank_hom_eq_zero 1 one_ne_zero (by decide)]
  norm_num

end IsSphericalObject

/-! ### Crossing to the numerical layer

`Numerical.K3.isSpherical_mukaiVector_iff` lives over a `NumericalVarietyData`
and knows nothing about `Dᵇ(Coh X)`. Crossing between them is
Hirzebruch--Riemann--Roch: the categorical Euler characteristic of an object
equals the numerical one of its class. That is not available at the pin, so it
is **supplied**, in the idiom of `Duality.Serre.DerivedStatement`. -/

variable (k) in
/-- The datum that identifies a categorical Euler characteristic with a
numerical one.

`chi₂_eq` is Hirzebruch--Riemann--Roch, restricted to the spherical objects
because `selfEuler` is only the intended invariant there. Nothing in this
repository constructs an `EulerRealization`; producing one is the geometric
obligation, and it is the same obligation `MukaiVector.lean` records for
`IntegralMukaiData`. -/
structure EulerRealization {A : Type*} {N : Type*} [CommRing A] [Algebra ℚ A]
    [AddCommGroup N] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [IsSmoothProperVariety k X] (V : Numerical.NumericalVarietyData 2 A N) where
  /-- The class of an object in the numerical Grothendieck group. -/
  cls : DerivedCat X → N
  /-- The two Euler characteristics agree on spherical objects. -/
  chi₂_eq : ∀ E : DerivedCat X, IsSphericalObject E →
    V.chi₂ (cls E) (cls E) = (selfEuler E : ℚ)

namespace IsSphericalObject

/-- **A spherical object has a spherical Mukai vector.**

The forward direction of the correspondence between the categorical and the
lattice-theoretic notions: `selfEuler_eq_two` computes `χ(E,E) = 2`, the
realization carries that to the numerical layer, and
`isSpherical_mukaiVector_iff` turns it into `⟪v(E), v(E)⟫ = -2`.

The converse is the hard direction and is not proved: `MukaiVector.lean` records
that it needs simplicity and Serre duality. -/
theorem isSpherical_mukaiVector {A : Type*} {N : Type*} {Λ : Type*} [CommRing A]
    [Algebra ℚ A] [AddCommGroup N] [AddCommGroup Λ] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X]
    {V : Numerical.NumericalVarietyData 2 A N} (R : EulerRealization k X V)
    (D : Numerical.K3.IntegralMukaiData V Λ) (hHRR : V.SatisfiesHRR)
    (hK3 : Numerical.K3.IsK3 V) {E : DerivedCat X} (h : IsSphericalObject E) :
    Mukai.IsSpherical D.b (D.mukaiVector (R.cls E)) := by
  rw [D.isSpherical_mukaiVector_iff hHRR hK3, R.chi₂_eq E h, h.selfEuler_eq_two]
  norm_num

end IsSphericalObject

end K3Surface

end AlgebraicGeometry
