/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Hausdorff
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.OrbitSpace
import Mathlib.Topology.Covering.Quotient

/-!
# Proper discontinuity of the autoequivalence action

This file isolates the geometric and topological input needed to treat the
compatible-autoequivalence action on a Bridgeland stability space as properly
discontinuous.  At the generality of `StabilityCondition.WithClassMap C v`,
that input is not a theorem: it is packaged explicitly in
`ProperDiscontinuityData`.

From the supplied data we derive finite point stabilizers, the standard local
neighbourhood consequences, Hausdorff separation of the orbit space, and the
covering-map statement over the image of the free locus.  The last result is
deliberately restricted.  Proper discontinuity makes point stabilizers finite,
but does not make the action free, so it does not imply an unrestricted
covering map.

The finite-stabilizer theorem below takes only the first field's Mathlib class.
The local and quotient consequences install the surjectivity-derived Hausdorff
instance and local compactness, while consuming the canonical continuous
constant-action instance from the combined-topology layer; keeping that split
visible prevents an accidental strengthening of the supplied geometric
interface.

## Missing geometric input

No inhabitant of `ProperDiscontinuityData` is constructed here.  A geometric
construction would require arithmetic control of the image of compatible
autoequivalences in lattice isometries, local finiteness for the corresponding
walls on the stability space, and finite-dimensionality sufficient to deduce
local compactness.  Those inputs are absent from the generic stability API.

Proper discontinuity here gives finite stabilizers of individual stability
conditions, but does not by itself give finiteness of a chamber's setwise
stabilizer.  A chamber-level statement needs a specified chamber action and
additional control of that action; none is asserted here.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped Topology

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

noncomputable section

open scoped GroupAction

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- External input asserting proper discontinuity and the two hypotheses
needed for its Hausdorff-local consequences on the stability space. -/
structure ProperDiscontinuityData (v : K₀ C →+ Λ) : Prop where
  /-- The compatible-autoequivalence action is properly discontinuous. -/
  properlyDiscontinuous :
    ProperlyDiscontinuousSMul (AutPairQuot v)
      (StabilityCondition.WithClassMap C v)
  /-- The class map is surjective, so the installed stability topology is
  Hausdorff. -/
  surjective : Function.Surjective v
  /-- The stability space is locally compact.  This does not follow from the
  current local-homeomorphism API without a finite-dimensionality input. -/
  locallyCompact : LocallyCompactSpace (StabilityCondition.WithClassMap C v)

/-- Proper discontinuity alone makes every point stabilizer finite.

This helper intentionally takes the Mathlib class directly: surjectivity and
local compactness are not needed for the point-stabilizer consequence. -/
theorem finite_stabilizer_of_properlyDiscontinuousSMul
    (h : ProperlyDiscontinuousSMul (AutPairQuot v)
      (StabilityCondition.WithClassMap C v))
    (σ : StabilityCondition.WithClassMap C v) :
    (MulAction.stabilizer (AutPairQuot v) σ : Set (AutPairQuot v)).Finite := by
  letI := h
  exact ProperlyDiscontinuousSMul.finite_stabilizer σ

/-- Compatibility wrapper for clients that already hold the complete external
data bundle.  Use `finite_stabilizer_of_properlyDiscontinuousSMul` when only
proper discontinuity is available. -/
theorem ProperDiscontinuityData.finite_stabilizer
    (d : ProperDiscontinuityData v)
    (σ : StabilityCondition.WithClassMap C v) :
    (MulAction.stabilizer (AutPairQuot v) σ : Set (AutPairQuot v)).Finite :=
  finite_stabilizer_of_properlyDiscontinuousSMul d.properlyDiscontinuous σ

/-- Every stability condition has a neighbourhood whose translates can meet
it only under elements fixing the original point. -/
theorem ProperDiscontinuityData.exists_nhds_image_smul_eq_self
    (d : ProperDiscontinuityData v)
    (σ : StabilityCondition.WithClassMap C v) :
    ∃ U ∈ 𝓝 σ, ∀ q : AutPairQuot v,
      (((q • ·) '' U) ∩ U).Nonempty → q • σ = σ := by
  letI := d.properlyDiscontinuous
  letI := d.locallyCompact
  letI := CategoryTheory.Triangulated.t2Space_withClassMap d.surjective
  exact ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self
    (AutPairQuot v) σ

/-- Every stability condition has a neighbourhood disjoint from each
translate whose group element does not fix the original point. -/
theorem ProperDiscontinuityData.exists_nhds_disjoint_image
    (d : ProperDiscontinuityData v)
    (σ : StabilityCondition.WithClassMap C v) :
    ∃ U ∈ 𝓝 σ, ∀ q : AutPairQuot v,
      q • σ ≠ σ → Disjoint ((q • ·) '' U) U := by
  letI := d.properlyDiscontinuous
  letI := d.locallyCompact
  letI := CategoryTheory.Triangulated.t2Space_withClassMap d.surjective
  exact ProperlyDiscontinuousSMul.exists_nhds_disjoint_image
    (AutPairQuot v) σ

/-- A properly discontinuous compatible-autoequivalence quotient is
Hausdorff under the supplied local-compactness and surjectivity inputs. -/
theorem ProperDiscontinuityData.t2Space_autPairOrbitSpace
    (d : ProperDiscontinuityData v) : T2Space (AutPairOrbitSpace v) := by
  letI := d.properlyDiscontinuous
  letI := d.locallyCompact
  letI := CategoryTheory.Triangulated.t2Space_withClassMap d.surjective
  exact inferInstance

/-- The compatible-autoequivalence orbit projection is a covering map over
the image of the free locus.  No covering claim is made at points with
nontrivial stabilizer. -/
theorem ProperDiscontinuityData.isCoveringMapOn_autPairOrbitMap
    (d : ProperDiscontinuityData v) :
    IsCoveringMapOn (autPairOrbitMap (C := C) (v := v))
      ((autPairOrbitMap (C := C) (v := v)) ''
        {σ | MulAction.stabilizer (AutPairQuot v) σ = ⊥}) := by
  letI := d.properlyDiscontinuous
  letI := d.locallyCompact
  letI := CategoryTheory.Triangulated.t2Space_withClassMap d.surjective
  exact isCoveringMapOn_quotientMk_of_properlyDiscontinuousSMul

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
