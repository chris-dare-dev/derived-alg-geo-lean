import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.BasicOpen
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Comparison
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Epi
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Extension
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Finiteness
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Gluing

/-!
# Affine module comparison

Mathlib provides the affine-scheme, quasi-coherent module-sheaf, and general localization-criterion
foundations; this directory retains a local formulation using
`AlgebraicGeometry.Scheme.Modules.basicOpenRestriction` and adds
basic-open presentation covers and bridges. See the
[affine and projective spectrum placement map](../../../docs/architecture/placement.md) for the
source owners and the existing Proj chart dependency.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.basicOpenRestriction` is restriction of global sections to a
  basic open.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_iff_isLocalizedModule` characterizes the
  counit by localization on every basic open, restating Mathlib's
  `AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing` in terms of this directory's explicit
  restriction map.
* `AlgebraicGeometry.Scheme.Modules.exists_basicOpen_presentation_cover` refines a quasi-coherent
  presentation cover to a basic-open cover.

## Implementation notes

This umbrella re-exports `BasicOpen`, `Comparison`, `Epi`, `Equivalence`, `Extension`,
`Finiteness`, and `Gluing`. Mathlib owns the `AlgebraicGeometry.IsLocalizing` predicate and its
whole-counit equivalence; the local API restates it using
`AlgebraicGeometry.Scheme.Modules.basicOpenRestriction`. The local files also provide
presentation-cover and DerivedAlgGeo-specific bridges.
Projective module charts consume `Extension` through
`AlgebraicGeometry/ProjectiveSpectrum/Modules/ChartExtension.lean`.

## References

* [Stacks, Tag 01IA](https://stacks.math.columbia.edu/tag/01IA), for the affine
  quasi-coherent comparison.
* See the [affine and projective spectrum placement map](../../../docs/architecture/placement.md)
  for pinned Mathlib source links.

## Tags

affine scheme, basic opens, quasi-coherent sheaves, global sections, localization,
module presentations
-/
