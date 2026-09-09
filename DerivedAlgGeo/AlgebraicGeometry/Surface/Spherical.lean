/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Linear
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.MukaiVector
import DerivedAlgGeo.AlgebraicGeometry.Surface.K3

/-!
# The spherical Ext profile on a smooth proper surface

`SphericalExtProfile E` says that the graded self-`Hom` algebra of an object `E`
of `Dᵇ(Coh X)` is that of a two-sphere:

```
Hom(E, E⟦i⟧) ≅ k   for i = 0 and i = 2,      and 0 otherwise.
```

This is the `n = 2` case of `CategoryTheory.SerreFunctor.SphericalExtProfile`,
restated for a scheme-derived category where no Serre functor is available. The
name matches that one deliberately.

## What this is, and what it is not

**It is not sphericity in general.** Huybrechts, *Fourier--Mukai Transforms in
Algebraic Geometry*, Definition 8.1 — equivalently Seidel--Thomas, *Braid group
actions on derived categories of coherent sheaves*, Definition 1.1 — has two
clauses, and this structure is only the second:

1. `E ⊗ ω_X ≅ E`, and
2. the Ext profile displayed above.

**The two coincide exactly when `ω_X ≅ O_X`**, in particular on a K3, where
`IsK3Surface.canonicalClass_eq_one` makes clause 1 automatic. That coincidence
is the motivation for this file and the reason it is filed under `K3Surface`,
but it is **not a hypothesis of any declaration here**: the variable block asks
only for `IsSmoothProperVariety k X`, and every theorem below is proved at that
generality. Keeping it there is deliberate — the profile and its consequences
are worth having for any smooth proper `X` — so the honest name is the one
above, not `IsSphericalObject`.

**Outside that case the profile is strictly weaker, and non-vacuously so.** On a
non-K3 surface with `q = 0` and `p_g = 1`, for instance one of general type, the
structure sheaf has `End(O_X) = k`, `Ext¹(O_X, O_X) = H¹(O_X) = 0` and
`Ext²(O_X, O_X) = H²(O_X) = k`, so it satisfies every field below; but
`ω_X ≇ O_X` there, so it is not spherical and its twist is not an
autoequivalence. Do not read a `SphericalExtProfile` on an arbitrary smooth
proper variety as a spherical object.

Dropping clause 1 is also what lets this file avoid a derived tensor product
entirely. Formalizing clause 1 for a general `X` waits on `⊗ᴸ`.

## Why it is expressible at all

`Hom(E, E⟦i⟧) ≅ k` is not a statement about an abelian group. Until
`CoherentSheaf/Linear.lean` constructed the `k`-linear structure on `Coh X` — and
Mathlib carried it to `Dᵇ(Coh X)` — the right-hand side had no meaning here, and
`Numerical/GrothendieckGroup/MukaiVector.lean` said as much in its docstring:
the Ext profile of an *object* needs an `Ext` that layer does not have. This
file is that docstring's target.

## What is a hypothesis, and what that costs

`end_one` and `ext_two` are **fields, not theorems**. Nothing here proves that
any particular object has one-dimensional endomorphisms; finite-dimensionality
of `Hom` in `Dᵇ(Coh X)` is not available (issue #332, behind the S1--S4
Serre-finiteness chain), so a `Hom`-group is a `k`-vector space of unknown
dimension until someone supplies otherwise.

The consequence is worth stating plainly: this file **defines** the profile and
proves the handful of things that follow from the definition alone. It does not
exhibit an object satisfying it, and it cannot, because exhibiting one means
computing a `Hom`-group.

## What is deliberately absent

* **No spherical twist.** `T_E` needs the evaluation triangle and a functorial
  cone; cones are not functorial in a triangulated category. See the scope notes
  on the dg-enhancement route (issue #378).
* **No Serre duality.** On a K3, `Hom(E, E⟦2⟧) ≅ Hom(E, E)ᵛ` would make
  `ext_two` follow from `end_one`, which is exactly how the literature states
  sphericity as "simple and rigid". `Duality/Serre/` carries duality as
  realization data, not as a theorem, so the two clauses stay independent here.
* **No K3 hypothesis, and so no claim of sphericity.** See the opening section.

## Main results

* `SphericalExtProfile` — the definition.
* `SphericalExtProfile.not_isZero` — an object with the profile is nonzero. The
  one thing that follows from `end_one` with no further input, and the reason
  the definition is not vacuous on the zero object.
* `SphericalExtProfile.finrank_end` — `dimₖ End(E) = 1`.
* `SphericalExtProfile.of_iso` — the profile is invariant under isomorphism.
* `SphericalExtProfile.selfEuler_eq_two` — `χ(E,E) = 1 - 0 + 1 = 2`, computed
  from the definition rather than assumed.
* `SphericalExtProfile.isSpherical_mukaiVector` — an object with the profile has
  a spherical Mukai vector, given an `EulerRealization`.

## A trap worth recording

The vanishing clause says `∀ f : E ⟶ E⟦i⟧, f = 0`, and **not**
`IsZero (E ⟶ E⟦i⟧)`. The second is well-typed and always false: `E ⟶ E⟦i⟧` is a
bare `Type`, `IsZero` there asks for an object that is both initial and
terminal, and `Type` has none — `Empty` and `PUnit` are different. Writing it
that way compiles and makes the whole structure uninhabitable, so every theorem
about the profile becomes vacuously true.

`IsK3Surface.h1_vanishing` *does* use `IsZero`, correctly, because
`Cohomology.coherentH` lands in `AddCommGrpCat`, which has a zero object. The
difference is the target category, not the mathematics.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

namespace K3Surface

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k X]

/-- The bounded derived category of coherent sheaves on a smooth proper `X`.

An abbreviation for readability only; everything about it comes from
`AlgebraicGeometry.DerivedCategory.SchemeBoundedCoherentDerivedCategory`. It
assumes no K3 hypothesis, despite the namespace. -/
abbrev DerivedCat : Type _ := SchemeBoundedCoherentDerivedCategory X

variable {X}

/-- **The spherical Ext profile of an object of `Dᵇ(Coh X)`.**

Clause 2 of Huybrechts' Definition 8.1. On a K3, where `ω_X ≅ O_X` discharges
clause 1, this *is* sphericity; on an arbitrary smooth proper `X` it is strictly
weaker, and the module docstring gives the counterexample. `end_one` and
`ext_two` are hypotheses, and what that costs is also in the module
docstring. -/
structure SphericalExtProfile (E : DerivedCat X) : Prop where
  /-- `Hom(E, E⟦i⟧) = 0` away from degrees `0` and `2`. Stated as "every
  morphism is zero" rather than `IsZero`; see the trap in the module
  docstring. -/
  vanishing : ∀ i : ℤ, i ≠ 0 → i ≠ 2 → ∀ f : E ⟶ E⟦i⟧, f = 0
  /-- `End(E) ≅ k`: the object is simple. Existence of an isomorphism, so that
  the profile is a property and not a choice of one. -/
  end_one : Nonempty ((E ⟶ E) ≃ₗ[k] k)
  /-- `Hom(E, E⟦2⟧) ≅ k`. On a K3 this is Serre-dual to `end_one`, but duality
  is realization data here, so it is asked for separately. -/
  ext_two : Nonempty ((E ⟶ E⟦(2 : ℤ)⟧) ≃ₗ[k] k)

namespace SphericalExtProfile

variable {E F : DerivedCat X} (h : SphericalExtProfile (k := k) E)

include h

/-- **An object with the spherical Ext profile is nonzero.**

If `E` were a zero object its endomorphism group would be a subsingleton, and
`end_one` would make `k` one too — impossible for a field. This is the only
consequence of `end_one` that needs no finiteness input, and it is what stops
the definition being satisfied vacuously. -/
theorem not_isZero : ¬ IsZero E := by
  intro hE
  have hsub : Subsingleton (E ⟶ E) := ⟨fun f g => hE.eq_of_src f g⟩
  have : Subsingleton k := h.end_one.some.toEquiv.symm.subsingleton
  exact (not_subsingleton k) this

/-- The endomorphism algebra is one-dimensional. -/
theorem finrank_end : Module.finrank k (E ⟶ E) = 1 := by
  rw [h.end_one.some.finrank_eq, Module.finrank_self]

/-- `Hom(E, E⟦2⟧)` is one-dimensional. -/
theorem finrank_ext_two : Module.finrank k (E ⟶ E⟦(2 : ℤ)⟧) = 1 := by
  rw [h.ext_two.some.finrank_eq, Module.finrank_self]

/-- **The profile is invariant under isomorphism.**

Transport along `Linear.homCongr`, which is the `k`-linear isomorphism of
`Hom`-groups induced by isomorphisms of source and target; the target side is
the isomorphism shifted. -/
theorem of_iso (e : E ≅ F) : SphericalExtProfile (k := k) F where
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

The profile forces the self-Euler characteristic to be `2`, which is exactly the
numerical condition `Numerical.K3.isSpherical_mukaiVector_iff` characterises.
Computing it needs nothing beyond the definition: the alternating sum has three
terms, and the profile gives all three.

**Only the forward direction.** `MukaiVector.lean` is explicit that recovering
the profile of an *object* from `χ(E,E) = 2` needs simplicity and Serre duality;
that converse is not attempted here and is not available. What follows is the
easy direction, and it is the one that connects this file to the lattice theory
in `LinearAlgebra/Lattice/Mukai/`. -/

/-- Degrees other than `0` and `2` contribute nothing. -/
theorem finrank_hom_eq_zero (i : ℤ) (hi₀ : i ≠ 0) (hi₂ : i ≠ 2) :
    Module.finrank k (E ⟶ E⟦i⟧) = 0 := by
  have : Subsingleton (E ⟶ E⟦i⟧) :=
    ⟨fun f g => by rw [h.vanishing i hi₀ hi₂ f, h.vanishing i hi₀ hi₂ g]⟩
  exact Module.finrank_zero_of_subsingleton

end SphericalExtProfile

/-- `χ(E, E)` in the only three degrees where `Hom` can be nonzero.

A definition for every object, but only the intended invariant for one whose
`Hom`-groups vanish outside `0, 1, 2` — which is what the profile supplies. It
is not claimed to agree with any numerical Euler pairing; that comparison is
`EulerRealization`. -/
noncomputable def selfEuler {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [IsSmoothProperVariety k X] (E : DerivedCat X) : ℤ :=
  (Module.finrank k (E ⟶ E) : ℤ)
    - (Module.finrank k (E ⟶ E⟦(1 : ℤ)⟧) : ℤ)
    + (Module.finrank k (E ⟶ E⟦(2 : ℤ)⟧) : ℤ)

namespace SphericalExtProfile

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X]
  {E : DerivedCat X} (h : SphericalExtProfile E)

include h

/-- **An object with the profile has self-Euler characteristic `2`.**

`1 - 0 + 1`. Every term comes from the definition: the outer two from `end_one`
and `ext_two`, the middle from `vanishing`. -/
theorem selfEuler_eq_two : selfEuler E = 2 := by
  rw [selfEuler, h.finrank_end, h.finrank_ext_two,
    h.finrank_hom_eq_zero 1 one_ne_zero (by decide)]
  norm_num

end SphericalExtProfile

/-! ### Crossing to the numerical layer

`Numerical.K3.isSpherical_mukaiVector_iff` lives over a `NumericalVarietyData`
and knows nothing about `Dᵇ(Coh X)`. Crossing between them is
Hirzebruch--Riemann--Roch: the categorical Euler characteristic of an object
equals the numerical one of its class. That is not available at the pin, so it
is **supplied**, in the idiom of `Duality.Serre.DerivedStatement`. -/

variable (k) in
/-- The datum that identifies a categorical Euler characteristic with a
numerical one.

`chi₂_eq` is Hirzebruch--Riemann--Roch, restricted to the objects with the
profile because `selfEuler` is only the intended invariant there. Nothing in this
repository constructs an `EulerRealization`; producing one is the geometric
obligation, and it is the same obligation `MukaiVector.lean` records for
`IntegralMukaiData`. -/
structure EulerRealization {A : Type*} {N : Type*} [CommRing A] [Algebra ℚ A]
    [AddCommGroup N] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [IsSmoothProperVariety k X] (V : Numerical.NumericalVarietyData 2 A N) where
  /-- The class of an object in the numerical Grothendieck group. -/
  cls : DerivedCat X → N
  /-- The two Euler characteristics agree on objects with the profile. -/
  chi₂_eq : ∀ E : DerivedCat X, SphericalExtProfile E →
    V.chi₂ (cls E) (cls E) = (selfEuler E : ℚ)

namespace SphericalExtProfile

/-- **An object with the profile has a spherical Mukai vector.**

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
    (hK3 : Numerical.K3.IsK3 V) {E : DerivedCat X} (h : SphericalExtProfile E) :
    Mukai.IsSpherical D.b (D.mukaiVector (R.cls E)) := by
  rw [D.isSpherical_mukaiVector_iff hHRR hK3, R.chi₂_eq E h, h.selfEuler_eq_two]
  norm_num

end SphericalExtProfile

end K3Surface

end AlgebraicGeometry
