/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact

/-!
# Quasi-compact covers for open scheme morphisms

For any morphism property that implies an open underlying map, its covering precoverage agrees
with its quasi-compact covering precoverage. Applying `Precoverage.toGrothendieck` gives the
corresponding equality of Grothendieck topologies.

These are direct extensions of Mathlib's `AlgebraicGeometry/Sites/QuasiCompact.lean`. The fppf and
étale specializations are downstream in `DerivedAlgGeo.AlgebraicGeometry.Sites.Comparison`.
-/

namespace AlgebraicGeometry.Scheme

open CategoryTheory

universe u

/-- Open morphisms give the same covering families with or without the quasi-compact condition. -/
lemma precoverage_eq_propQCPrecoverage_of_isOpenMap {P : MorphismProperty Scheme.{u}}
    (hP : P ≤ fun _ _ f ↦ IsOpenMap f.base) :
    precoverage P = propQCPrecoverage P :=
  le_antisymm (le_inf (precoverage_le_qcPrecoverage_of_isOpenMap hP) le_rfl) inf_le_right

/-- The topology of an open-map morphism property agrees with its quasi-compact topology. -/
lemma grothendieckTopology_eq_propQCTopology_of_isOpenMap
    {P : MorphismProperty Scheme.{u}} (hP : P ≤ fun _ _ f ↦ IsOpenMap f.base) :
    grothendieckTopology P = propQCTopology P :=
  congrArg Precoverage.toGrothendieck (precoverage_eq_propQCPrecoverage_of_isOpenMap hP)

end AlgebraicGeometry.Scheme
