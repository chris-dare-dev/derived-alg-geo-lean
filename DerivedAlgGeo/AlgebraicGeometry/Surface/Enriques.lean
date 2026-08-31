/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Surface.K3

/-!
# Enriques surfaces

An Enriques surface is a smooth projective surface whose canonical class is
2-torsion but not trivial, with no first cohomology. This file says exactly
that, against the objects this repository already has:

* the surface is `X : SmoothProperVariety k` carrying a
  `CanonicalSheafData X 2`, exactly as for `IsK3Surface` — the dimension is
  the `2` in that package's `SmoothOfRelativeDimension`;
* "2-torsion canonical class" is the pair of group equations
  `C.canonicalClass ^ 2 = 1` and `C.canonicalClass ≠ 1` in `Pic X`, which
  need no torsion-Picard API: `Pic` is a group of units and the conditions
  are ordinary equations in it;
* "no first cohomology" is vanishing of `H¹(X, O_X)`, using the constructed
  functor `Cohomology.coherentH`, verbatim the `IsK3Surface` clause.

## The characteristic is not a field of the structure

Over a field of characteristic 2 the surfaces classically called Enriques
split into classical, singular, and supersingular types, and for some of them
`ω_X` is trivial, contradicting `canonicalClass_ne_one`. The definition here
is the characteristic `≠ 2` one, but the exclusion is *not* recorded as a
field: the source papers (Li--Nuer--Stellari--Zhao, arXiv:1912.04332, and
Li--Stellari--Zhao, arXiv:2104.13610) assume an algebraically closed field of
characteristic different from 2 theorem by theorem, and that is where the
hypothesis belongs. A characteristic field here would make every downstream
statement carry it even when unused.

## What this file does not do

* **It exhibits no Enriques surface.** Nothing here constructs an `X`, a
  `CanonicalSheafData X 2`, or an `IsEnriquesSurface`; every statement is
  conditional on data nobody has yet produced, exactly as for `IsK3Surface`.
* **It states no numerical consequence.** `χ(O_X) = 1` needs
  Hirzebruch--Riemann--Roch and `H²(X, O_X) = 0` needs Serre duality against
  the non-triviality of `ω_X`; neither exists at the pin, and
  `Duality/Serre/` carries the latter as realization data. The numerical
  shadow lives in `Numerical/Examples/Surface/`, with no bridge claimed.
* **It does not construct the K3 double cover.** The 2-torsion class
  classically determines an étale double cover with trivial canonical class;
  no covering machinery exists at the pin and none is stated.

## Main definitions

* `IsEnriquesSurface` — the `Prop`-valued definition, over a supplied
  canonical-sheaf package.
* `EnriquesSurface` — the bundled carrier, for callers who want one object.

## Main results

* `IsEnriquesSurface.canonicalSquare_iso` — the sheaf-level trivialization
  `ω_X ⊗ ω_X ≅ O_X` extracted from the class equation.
* `IsEnriquesSurface.canonicalSheaf_not_iso_unit` — non-triviality at the
  sheaf level, through `canonicalClass_eq_one_iff`.
* `IsEnriquesSurface.antiCanonicalClass_eq_canonicalClass` — a 2-torsion
  class is its own inverse.
* `IsEnriquesSurface.not_isK3Surface` — the same canonical-sheaf package
  cannot witness both definitions.

## References

* Li, Nuer, Stellari, Zhao, *A refined Derived Torelli Theorem for Enriques
  surfaces*, arXiv:1912.04332.
* Li, Stellari, Zhao, *A refined Derived Torelli Theorem for Enriques
  surfaces, II: the non-generic case*, arXiv:2104.13610.

## Tags

Enriques surface, canonical class, torsion, Picard group
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace SmoothProperVariety

variable {k : Type u} [Field k] {X : SmoothProperVariety k}

/-! ### The definition -/

/-- **An Enriques surface**: a smooth projective surface whose canonical class
is 2-torsion but not trivial, with vanishing first cohomology.

`Prop`-valued over a chosen `CanonicalSheafData X 2`, for the same reason as
`IsK3Surface`: the canonical-sheaf package is genuine data, so bundling it
into the predicate would make "being an Enriques surface" depend on a choice.
The torsion conditions are ordinary group equations in `Pic X`; no
torsion-subgroup API is involved. The characteristic `≠ 2` hypothesis of the
classical theory is deliberately absent — see the module docstring. -/
structure IsEnriquesSurface (X : SmoothProperVariety k)
    (C : X.CanonicalSheafData 2) : Prop where
  /-- The surface is projective. Stronger than the properness already carried
  by `SmoothProperVariety`, and the standard hypothesis of the source papers. -/
  projective : X.toVariety.IsProjective
  /-- `ω_X` is 2-torsion in `Pic X`. Equivalently, by `canonicalSquare_iso`,
  there is an isomorphism `ω_X ⊗ ω_X ≅ O_X`. -/
  canonicalClass_sq_eq_one : C.canonicalClass ^ 2 = 1
  /-- `ω_X` is not trivial in `Pic X`. This is what separates an Enriques
  surface from a K3 surface; see `not_isK3Surface`. -/
  canonicalClass_ne_one : C.canonicalClass ≠ 1
  /-- `H¹(X, O_X) = 0`. -/
  h1_vanishing :
    IsZero ((Cohomology.coherentH X.toVariety.toScheme 1).obj
      (Scheme.structureSheafCoh X.toVariety.toScheme))

namespace IsEnriquesSurface

variable {C : X.CanonicalSheafData 2} (h : IsEnriquesSurface X C)

include h

/-- **The square of the canonical sheaf of an Enriques surface is trivial**, at
the sheaf level.

The class equation `κ² = 1` is unpacked through
`Scheme.Modules.LineBundleData.toPic_tensor` and
`Scheme.Modules.LineBundleData.toPic_eq_iff`; the recorded tensor inverses
play no part, which is why a bare `Nonempty` of isomorphisms comes out. -/
theorem canonicalSquare_iso :
    Nonempty
      (Scheme.Modules.tensorObj C.canonicalSheaf C.canonicalSheaf ≅
        (Scheme.structureSheafCoh X.toVariety.toScheme).obj) := by
  have hsq :
      (C.canonicalLineBundle.tensor C.canonicalLineBundle).toPic =
        (Scheme.Modules.LineBundleData.unit X.toVariety.toScheme).toPic := by
    rw [Scheme.Modules.LineBundleData.toPic_tensor,
      Scheme.Modules.LineBundleData.unit_toPic, ← pow_two]
    exact h.canonicalClass_sq_eq_one
  exact (Scheme.Modules.LineBundleData.toPic_eq_iff _ _).1 hsq

/-- **The canonical sheaf of an Enriques surface is not trivial**, at the sheaf
level. The contrapositive of `canonicalClass_eq_one_iff` applied to
`canonicalClass_ne_one`. -/
theorem canonicalSheaf_not_iso_unit :
    ¬ Nonempty
      (C.canonicalSheaf ≅
        (Scheme.structureSheafCoh X.toVariety.toScheme).obj) :=
  fun e =>
    h.canonicalClass_ne_one ((CanonicalSheafData.canonicalClass_eq_one_iff C).2 e)

/-- **A 2-torsion canonical class is its own inverse**: the anticanonical class
of an Enriques surface equals its canonical class. This is the form in which
the 2-torsion hypothesis is consumed by Serre-duality statements, where
twisting by `ω_X` and by `ω_X⁻¹` must agree. -/
theorem antiCanonicalClass_eq_canonicalClass :
    C.antiCanonicalLineBundle.toPic = C.canonicalClass := by
  rw [C.antiCanonicalClass]
  exact inv_eq_of_mul_eq_one_right (by
    rw [← pow_two]; exact h.canonicalClass_sq_eq_one)

/-- **No canonical-sheaf package witnesses both definitions**: an Enriques
surface is not a K3 surface. The two definitions disagree exactly at
triviality of the canonical class, and this pins them against each other on
the shared carrier. -/
theorem not_isK3Surface : ¬ IsK3Surface X C :=
  fun hK3 => h.canonicalClass_ne_one hK3.canonicalClass_eq_one

end IsEnriquesSurface

end SmoothProperVariety

/-! ### The bundled object -/

/-- An Enriques surface over `k`, with its canonical-sheaf package and the
Enriques property bundled together.

Callers that only need "let `Y` be an Enriques surface" want this; callers
proving things about a fixed canonical package want `IsEnriquesSurface`
directly. Nothing in this repository constructs one. -/
structure EnriquesSurface (k : Type u) [Field k] where
  /-- The underlying smooth proper variety. -/
  toSmoothProperVariety : SmoothProperVariety k
  /-- Its chosen canonical-sheaf package in dimension two. -/
  canonical : toSmoothProperVariety.CanonicalSheafData 2
  /-- The Enriques conditions. -/
  isEnriques :
    SmoothProperVariety.IsEnriquesSurface toSmoothProperVariety canonical

namespace EnriquesSurface

variable {k : Type u} [Field k] (Y : EnriquesSurface k)

/-- The underlying variety. -/
abbrev toVariety : Variety k := Y.toSmoothProperVariety.toVariety

/-- The underlying scheme. -/
abbrev toScheme : Scheme.{u} := Y.toVariety.toScheme

/-- Named rather than anonymous, following `K3Surface.instIsProjective`: the
generated name of an anonymous instance here is derived from `toVariety`, so
renaming that field would silently move an audited declaration. -/
instance instIsProjective : Y.toVariety.IsProjective := Y.isEnriques.projective

/-- The square of the canonical sheaf of an Enriques surface is trivial. -/
theorem canonicalSquare_iso :
    Nonempty
      (Scheme.Modules.tensorObj Y.canonical.canonicalSheaf
          Y.canonical.canonicalSheaf ≅
        (Scheme.structureSheafCoh Y.toScheme).obj) :=
  Y.isEnriques.canonicalSquare_iso

/-- The canonical sheaf of an Enriques surface is not trivial. -/
theorem canonicalSheaf_not_iso_unit :
    ¬ Nonempty
      (Y.canonical.canonicalSheaf ≅
        (Scheme.structureSheafCoh Y.toScheme).obj) :=
  Y.isEnriques.canonicalSheaf_not_iso_unit

/-- `H¹(Y, O_Y) = 0`. -/
theorem h1_vanishing :
    IsZero ((Cohomology.coherentH Y.toScheme 1).obj
      (Scheme.structureSheafCoh Y.toScheme)) :=
  Y.isEnriques.h1_vanishing

end EnriquesSurface

end AlgebraicGeometry
