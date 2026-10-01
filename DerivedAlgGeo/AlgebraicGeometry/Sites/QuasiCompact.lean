/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact

/-!
# Quasi-compact covers for open scheme morphisms

For any morphism property that implies an open underlying map, its covering precoverage agrees
with its quasi-compact covering precoverage. The fppf and étale specializations live downstream
in `DerivedAlgGeo.AlgebraicGeometry.Sites.Comparison`.

## Main results

* `AlgebraicGeometry.Scheme.precoverage_eq_propQCPrecoverage_of_isOpenMap` identifies the
  covering precoverages under the open-map criterion.
* `AlgebraicGeometry.Scheme.grothendieckTopology_eq_propQCTopology_of_isOpenMap` identifies
  their generated topologies.

## Implementation notes

Quasi-compactness here concerns covering families, rather than each individual arrow. Mathlib's
open-map inclusion supplies finite local refinements; lattice antisymmetry gives the equality.
Applying `CategoryTheory.Precoverage.toGrothendieck` transports it to the topology level.

## References

Mathlib's `AlgebraicGeometry/Sites/QuasiCompact.lean` owns the covering condition and the
open-map inclusion used here.

## Tags

schemes, covering families, quasi-compact topology
-/

namespace AlgebraicGeometry.Scheme

open CategoryTheory

universe u

/-- Openness supplies the finite local refinements required by the quasi-compact covering
condition; the individual morphisms need not be quasi-compact. -/
lemma precoverage_eq_propQCPrecoverage_of_isOpenMap {P : MorphismProperty Scheme.{u}}
    (hP : P ≤ fun _ _ f ↦ IsOpenMap f.base) :
    precoverage P = propQCPrecoverage P :=
  le_antisymm (le_inf (precoverage_le_qcPrecoverage_of_isOpenMap hP) le_rfl) inf_le_right

/-- Transport the equality of covering precoverages through
`CategoryTheory.Precoverage.toGrothendieck`; no additional stability or multiplicativity
assumption on the morphism property is required. -/
lemma grothendieckTopology_eq_propQCTopology_of_isOpenMap
    {P : MorphismProperty Scheme.{u}} (hP : P ≤ fun _ _ f ↦ IsOpenMap f.base) :
    grothendieckTopology P = propQCTopology P :=
  congrArg Precoverage.toGrothendieck (precoverage_eq_propQCPrecoverage_of_isOpenMap hP)

end AlgebraicGeometry.Scheme
