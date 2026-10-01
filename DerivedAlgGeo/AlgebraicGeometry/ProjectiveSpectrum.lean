import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.BasicOpenLemmas
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Integral
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveSpaceProperties
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveSpaceVariety
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.StructureSections

/-!
# Graded modules and associated sheaves on projective spectra

Mathlib supplies `AlgebraicGeometry.Proj` as a scheme, its standard affine charts, their affine
cover, and the structure map to `AlgebraicGeometry.Spec` of the degree-zero ring. This library
develops further geometric and module-sheaf results on those charts. See the
[affine and projective spectrum placement map](../../docs/architecture/placement.md) for the
pinned owners and the concrete connection to the affine module API.

## Main definitions

* `AlgebraicGeometry.Proj.chartRing` bundles Mathlib's homogeneous chart ring as `CommRingCat`.
* `AlgebraicGeometry.Proj.awayRestrict` restricts a module sheaf along the existing standard chart
  immersion.

## Main results

* `AlgebraicGeometry.Proj.basicOpenIsoSpec` identifies a positive-degree standard chart with the
  spectrum of its degree-zero homogeneous localization.
* `AlgebraicGeometry.Proj.affineOpenCover` supplies the affine chart cover.
* `AlgebraicGeometry.Proj.toSpecZero` and
  `AlgebraicGeometry.Proj.awayι_toSpecZero` record the structure map and its restriction to a
  chart.

## Implementation notes

This umbrella re-exports `BasicOpenLemmas`, `Integral`, `Modules`, `ProjectiveSpaceProperties`,
`ProjectiveSpaceVariety`, and `StructureSections`. The local module-chart path is
`ProjectiveSpectrum/Modules/ChartExtension.lean` →
`AlgebraicGeometry/Modules/Affine/Extension.lean` → Mathlib's
`AlgebraicGeometry/Modules/Tilde.lean`. Its chart ring is
`HomogeneousLocalization.Away`, the degree-zero homogeneous localization, rather than the full
ordinary localization at the homogeneous element.

## References

* [Stacks, Tag 01M3: Proj of a graded ring, standard affine charts, and the map to
  `Spec A₀`](https://stacks.math.columbia.edu/tag/01M3).
* [nLab: projective schemes](https://ncatlab.org/nlab/show/projective+scheme).
* See the [affine and projective spectrum placement map](../../docs/architecture/placement.md)
  for pinned Mathlib source links.

## Tags

Proj, projective spectrum, standard opens, affine charts, homogeneous localization,
graded modules, sheaves
-/
