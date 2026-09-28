import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.BasicOpen
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Comparison
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Epi
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Extension
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Finiteness
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Gluing

/-!
# Affine module comparison

Mathlib provides the affine-scheme and quasi-coherent module-sheaf comparison foundations;
this directory adds localization criteria, basic-open presentation covers, and bridges. See the
[affine and projective spectrum placement map](../../../docs/architecture/placement.md) for the
source owners and the existing Proj chart dependency.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.basicOpenRestriction` is restriction of global sections to a
  basic open.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_iff_isLocalizedModule` characterizes the
  counit by localization on every basic open.
* `AlgebraicGeometry.Scheme.Modules.exists_basicOpen_presentation_cover` refines a quasi-coherent
  presentation cover to a basic-open cover.

## Implementation notes

This umbrella re-exports `BasicOpen`, `Comparison`, `Epi`, `Equivalence`, `Extension`,
`Finiteness`, and `Gluing`. The quasi-coherent affine comparison itself is upstream in Mathlib;
the local files provide a general localization criterion and DerivedAlgGeo-specific bridges.
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
