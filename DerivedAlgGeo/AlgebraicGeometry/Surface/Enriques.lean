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

* the surface is `X : Scheme` with `[IsSmoothProperVariety k X]` carrying a
  `CanonicalSheafData k X 2`, exactly as for `IsK3Surface` — the dimension is
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
  `CanonicalSheafData k X 2`, or an `IsEnriquesSurface`; every statement is
  conditional on data nobody has yet produced, exactly as for `IsK3Surface`.
* **It states no numerical consequence.** Both `H²(X, O_X) = 0` and
  `χ(O_X) = 1` reduce to one missing input: Serre duality against the
  non-triviality of `ω_X`. It gives `H²(X, O_X) ≅ H⁰(X, ω_X)^∨ = 0`, because
  a non-trivial torsion line bundle has no sections, and then
  `χ(O_X) = h⁰ - h¹ + h² = 1` needs nothing further. `Duality/Serre/` carries
  that duality as `DerivedStatement` realization data rather than as a
  theorem, so neither consequence is available at the pin. No numerical
  shadow exists either: `Numerical/Examples/Surface/` holds `Abelian`, `K3`,
  `ProjectivePlane`, and `RankOne`, and the Enriques `NumericalVarietyData 2`
  that would pair with them is not written.
* **It does not construct the K3 double cover.** The 2-torsion class
  classically determines an étale double cover with trivial canonical class;
  no covering machinery exists at the pin and none is stated.

## Main definitions

* `IsEnriquesSurface` — the `Prop`-valued definition, over a supplied
  canonical-sheaf package.
* `EnriquesSurface` — the bundled carrier, for callers who want one object.

## Main results

* `IsEnriquesSurface.canonicalSheaf_tensor_self_iso_unit` — the sheaf-level
  trivialization `ω_X ⊗ ω_X ≅ O_X` extracted from the class equation.
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

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X]

/-! ### The definition -/

variable (k) in
/-- **An Enriques surface**: a smooth projective surface whose canonical class
is 2-torsion but not trivial, with vanishing first cohomology.

`Prop`-valued over a chosen `CanonicalSheafData k X 2`, for the same reason as
`IsK3Surface`: the canonical-sheaf package is genuine data, so bundling it
into the predicate would make "being an Enriques surface" depend on a choice.
The torsion conditions are ordinary group equations in `Pic X`; no
torsion-subgroup API is involved. The characteristic `≠ 2` hypothesis of the
classical theory is deliberately absent — see the module docstring. -/
class IsEnriquesSurface (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X]
    (C : SmoothProperVariety.CanonicalSheafData k X 2) : Prop where
  /-- The surface is projective. Stronger than the properness already carried
  by `SmoothProperVariety`, and the standard hypothesis of the source papers. -/
  projective : Variety.IsProjective k X
  /-- `ω_X` is 2-torsion in `Pic X`. Equivalently, by
  `canonicalSheaf_tensor_self_iso_unit`, there is an isomorphism
  `ω_X ⊗ ω_X ≅ O_X`. -/
  canonicalClass_sq_eq_one : C.canonicalClass ^ 2 = 1
  /-- `ω_X` is not trivial in `Pic X`. This is what separates an Enriques
  surface from a K3 surface; see `not_isK3Surface`. -/
  canonicalClass_ne_one : C.canonicalClass ≠ 1
  /-- `H¹(X, O_X) = 0`. -/
  h1_vanishing :
    IsZero ((Cohomology.coherentH X 1).obj
      (Scheme.structureSheafCoh X))

namespace IsEnriquesSurface

variable {C : SmoothProperVariety.CanonicalSheafData k X 2} (h : IsEnriquesSurface k X C)

include h

/-- **The square of the canonical sheaf of an Enriques surface is trivial**, at
the sheaf level.

The class equation `κ² = 1` is unpacked through
`Scheme.Modules.LineBundleData.toPic_tensor` and
`Scheme.Modules.LineBundleData.toPic_eq_iff`; the recorded tensor inverses
play no part, which is why a bare `Nonempty` of isomorphisms comes out. -/
theorem canonicalSheaf_tensor_self_iso_unit :
    Nonempty
      (Scheme.Modules.tensorObj C.canonicalSheaf C.canonicalSheaf ≅
        (Scheme.structureSheafCoh X).obj) := by
  have hsq :
      (C.canonicalLineBundle.tensor C.canonicalLineBundle).toPic =
        (Scheme.Modules.LineBundleData.unit X).toPic := by
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
        (Scheme.structureSheafCoh X).obj) :=
  fun e =>
    h.canonicalClass_ne_one ((CanonicalSheafData.canonicalClass_eq_one_iff C).2 e)

/-- **A 2-torsion canonical class is its own inverse**: `κ⁻¹ = κ`, since
`κ * κ = 1`.

Stated for Serre duality, whose surface-level statements twist by `κ * L⁻¹`
(`Duality.Serre.SurfacePicardSymmetry`): on an Enriques surface the `ω_X` and
`ω_X⁻¹` twists coincide, so the two directions of the duality agree without a
case split. Nothing consumes it yet — those statements take the canonical
class as a bare `Pic` parameter and never see a `CanonicalSheafData`. -/
theorem antiCanonicalClass_eq_canonicalClass :
    C.antiCanonicalLineBundle.toPic = C.canonicalClass := by
  rw [C.antiCanonicalClass]
  exact inv_eq_of_mul_eq_one_right (by
    rw [← pow_two]; exact h.canonicalClass_sq_eq_one)

/-- **No canonical-sheaf package witnesses both definitions**: an Enriques
surface is not a K3 surface. The two definitions disagree exactly at
triviality of the canonical class, and this pins them against each other on
the shared carrier. -/
theorem not_isK3Surface : ¬ IsK3Surface k X C :=
  fun hK3 => h.canonicalClass_ne_one hK3.canonicalClass_eq_one

end IsEnriquesSurface

end SmoothProperVariety

/-! ### The bundled object

The three theorems below restate the `IsEnriquesSurface` results with the
canonical package implicit, so a caller holding an Enriques surface `Y` never
has to name `Y.canonical` to use them. They add no mathematics; every one is
`Y.isEnriques.<same name>`. -/

/-! ### No bundled object

As for K3 surfaces, "let `Y` be an Enriques surface" is
`(Y : Scheme) [Y.Over (Spec k)] [IsSmoothProperVariety k Y]
(C : CanonicalSheafData k Y 2) [IsEnriquesSurface k Y C]`; the former an Enriques surface over `k`
structure and its wrappers are gone, and `IsEnriquesSurface` holds the derived statements. -/

namespace EnriquesSurface

variable {k : Type u} [Field k] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k Y] {C : SmoothProperVariety.CanonicalSheafData k Y 2}

/-- An Enriques surface is projective. Not an instance, for the reason given at
`K3Surface.isProjective`. -/
theorem isProjective [h : SmoothProperVariety.IsEnriquesSurface k Y C] :
    Variety.IsProjective k Y :=
  h.projective

end EnriquesSurface

end AlgebraicGeometry
