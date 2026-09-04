/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.StructureSheaf
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.FiniteDimensional
import DerivedAlgGeo.AlgebraicGeometry.Duality.Canonical
import DerivedAlgGeo.AlgebraicGeometry.Variety.Projective

/-!
# K3 surfaces

A K3 surface is a smooth projective surface with trivial canonical bundle and
no first cohomology. This file says exactly that, against the objects this
repository already has:

* the surface is `X : Scheme` with `[IsSmoothProperVariety k X]` carrying a
  `CanonicalSheafData k X 2` — the dimension is the `2` in that package's
  `SmoothOfRelativeDimension`, so it is a hypothesis of the canonical-sheaf
  data rather than a separate numerical claim;
* "trivial canonical bundle" is `C.canonicalClass = 1` in `Pic X`, which
  `canonicalClass_eq_one_iff` shows is the same as an isomorphism
  `ω_X ≅ O_X`;
* "no first cohomology" is vanishing of `H¹(X, O_X)`, using the constructed
  functor `Cohomology.coherentH` rather than any supplied realization.

## The property is separated from the data

`IsK3Surface` is `Prop`-valued and takes the canonical-sheaf package as a
*parameter*. That mirrors `Numerical.K3.IsK3`, which is `Prop`-valued over a
`NumericalVarietyData`, and it is forced by the same consideration:
`CanonicalSheafData` is genuine data — its own docstring records that the
cotangent object and determinant descent are fields because the scheme-sheaf
API does not yet construct them — so bundling it into a predicate would make
"being a K3 surface" depend on a choice. `K3Surface` at the end of the file is
the bundle, for callers who want one object.

## Why projectivity is a field

The carrier a smooth proper variety over `k` already supplies properness, and
`Variety.isProper_of_isProjective` shows projectivity implies it, so the two
overlap. They are not interchangeable: projective is strictly stronger, and it
is the standard hypothesis in the K3 literature — Bridgeland's
`math/0307164` says *algebraic* K3 surface throughout and uses the ample cone
from the first construction onwards. The carrier stays `SmoothProperVariety`
because that is what `CanonicalSheafData` is indexed by; the extra strength
goes in the field.

## What this file does not do

* **It exhibits no K3 surface.** Nothing here constructs an `X`, a
  `CanonicalSheafData k X 2`, or an `IsK3Surface`. `Numerical/Examples/Surface/K3.lean`
  exhibits a *numerical* model — a `NumericalVarietyData 2` satisfying
  `Numerical.K3.IsK3` — and that is a model of the Todd-class axioms, not of
  anything below. Every statement here is conditional on data nobody has yet
  produced.
* **It does not connect to `Numerical.K3.IsK3`.** That bridge —
  `IsK3Surface k X C → NumericalVarietyData 2 A N` satisfying `IsK3` — is
  Hirzebruch–Riemann–Roch plus the Todd class of a K3, neither of which exists
  at the pin. When it arrives it must be a structure carrying the realization,
  in the idiom of `Duality.Serre.DerivedStatement`, and not a theorem. It is
  not stated here in any form, because a statement whose hypotheses cannot be
  written down is not a statement.
* **It proves no vanishing.** `h1_vanishing` is a hypothesis. In particular
  nothing here derives `H²(X, O_X) ≅ k` from it, which needs Serre duality
  against the triviality of `ω_X`; `Duality/Serre/` carries that as
  realization data.

## Main results

* `canonicalClass_eq_one_iff` — `C.canonicalClass = 1 ↔ Nonempty (ω_X ≅ O_X)`.
  This is what makes the Picard-group formulation of triviality the same as
  the sheaf-level one, and it holds for a `CanonicalSheafData` of any
  dimension.
* `IsK3Surface` — the definition.
* `IsK3Surface.canonicalSheaf_iso` — the isomorphism `ω_X ≅ O_X` extracted
  from a K3 witness.
* `IsK3Surface.antiCanonicalClass_eq_one` — the anticanonical class is trivial
  too.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace SmoothProperVariety

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}

/-! ### Triviality of the canonical class

`canonicalClass` lands in `Pic`, whose elements are isomorphism classes with a
recorded tensor inverse. Equality with `1` is therefore a statement about
classes; this section says it is equivalent to the sheaf-level isomorphism, so
that neither formulation has to be preferred downstream. -/

namespace CanonicalSheafData

omit [IsSmoothProperVariety k X] in
/-- **Trivial canonical class means a trivial canonical sheaf.**

The forward direction is the useful one: `canonicalClass = 1` is an equation in
a group and is what composes with the rest of the Picard API, while
`ω_X ≅ O_X` is what a geometric argument actually consumes. Stated for a
`CanonicalSheafData` in any dimension; nothing about surfaces enters. -/
theorem canonicalClass_eq_one_iff (C : SmoothProperVariety.CanonicalSheafData k X n) :
    C.canonicalClass = 1 ↔
      Nonempty (C.canonicalSheaf ≅
        (Scheme.structureSheafCoh X).obj) := by
  rw [show C.canonicalClass = C.canonicalLineBundle.toPic from rfl,
    ← Scheme.Modules.LineBundleData.unit_toPic X,
    Scheme.Modules.LineBundleData.toPic_eq_iff]
  -- `canonicalSheaf` and `structureSheafCoh.obj` are the two `line` fields by
  -- definition; only the spelling differs.
  exact Iff.rfl

end CanonicalSheafData

/-! ### The definition -/

variable (k) in
/-- **A K3 surface**: a smooth projective surface with trivial canonical bundle
and vanishing first cohomology.

`Prop`-valued over a chosen `CanonicalSheafData k X 2`; see the module docstring
for why the data is a parameter rather than a field, and why projectivity is a
field rather than an instance on the carrier. -/
class IsK3Surface (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] (C : SmoothProperVariety.CanonicalSheafData k X 2) :
    Prop where
  /-- The surface is projective. Stronger than the properness already carried
  by `SmoothProperVariety`; see the module docstring. -/
  projective : Variety.IsProjective k X
  /-- `ω_X` is trivial in `Pic X`. Equivalently, by `canonicalClass_eq_one_iff`,
  there is an isomorphism `ω_X ≅ O_X`. -/
  canonicalClass_eq_one : C.canonicalClass = 1
  /-- `H¹(X, O_X) = 0`. -/
  h1_vanishing :
    IsZero ((Cohomology.coherentH X 1).obj
      (Scheme.structureSheafCoh X))

namespace IsK3Surface

variable {C : SmoothProperVariety.CanonicalSheafData k X 2} (h : IsK3Surface k X C)

include h

/-- The canonical sheaf of a K3 surface is isomorphic to its structure sheaf. -/
theorem canonicalSheaf_iso :
    Nonempty (C.canonicalSheaf ≅
      (Scheme.structureSheafCoh X).obj) :=
  (CanonicalSheafData.canonicalClass_eq_one_iff C).1 h.canonicalClass_eq_one

/-- The anticanonical class of a K3 surface is trivial. -/
theorem antiCanonicalClass_eq_one :
    C.antiCanonicalLineBundle.toPic = 1 := by
  rw [C.antiCanonicalClass, h.canonicalClass_eq_one, inv_one]

end IsK3Surface

end SmoothProperVariety

/-! ### No bundled object

A caller that wants "let `X` be a K3 surface" writes
`(X : Scheme) [X.Over (Spec k)] [IsSmoothProperVariety k X]
(C : CanonicalSheafData k X 2) [IsK3Surface k X C]`, exactly as Mathlib writes
"let `X` be a proper scheme over `S`". The former a K3 surface over `k` structure bundled
those four things and is gone; its derived statements were `IsK3Surface.<name>`
with the package implicit, and `IsK3Surface` is where they live. -/

namespace K3Surface

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k X] {C : SmoothProperVariety.CanonicalSheafData k X 2}

/-- A K3 surface is projective. Not an instance: the canonical package `C` witnessing
`IsK3Surface` is not determined by the conclusion, so a caller supplies it. -/
theorem isProjective [h : SmoothProperVariety.IsK3Surface k X C] : Variety.IsProjective k X :=
  h.projective

end K3Surface

end AlgebraicGeometry


