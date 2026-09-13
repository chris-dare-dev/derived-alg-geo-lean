/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.AdjunctionComparison
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.EnhancedFunctor

/-!
# Adjoint-comparison conditions for enhanced functors

For an `EnhancedAdjunctionCones` package, the generic dg-cone layer constructs
the two canonical closed comparison transformations

`L T[-1] ⟶ R` and `R ⟶ C L`.

This file records the corresponding Anno--Logvinenko conditions at the
ordinary categorical boundary: both induced natural transformations on `H⁰`
are isomorphisms.  The fields use Mathlib's `IsIso` predicate on the canonical
maps themselves, rather than storing unrelated natural isomorphisms.

These conditions do not imply sphericality in this repository.  In
particular, nothing here derives them from `TwistCotwistEquivalenceConditions`
or supplies the Morita quasi-functor and higher cone coherence needed for the
two-of-four theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory DGCategoryStruct DGCategory

variable {A : Type u} {B : Type u'}
  [DGCategory.{v} A] [DGCategory.{v} B]
  {S : DGFunctor A B} {L R : DGFunctor B A}

/-- The two adjoint-comparison conditions for selected enhanced cones.

They assert invertibility only after passage to `H⁰`, and only for the
canonical maps constructed from the selected cone and adjunction data. -/
structure AdjointComparisonConditions
    (P : EnhancedAdjunctionCones S L R) [IsPretriangulated B] : Prop where
  /-- The canonical comparison `L T[-1] ⟶ R` is invertible on `H⁰`. -/
  twist : IsIso
    (DGAdjunction.CounitConeData.twistAdjointComparison_h0
      (rightAdj := P.rightAdj) P.leftAdj P.twist)
  /-- The canonical comparison `R ⟶ C L` is invertible on `H⁰`. -/
  cotwist : IsIso
    (DGAdjunction.UnitConeData.cotwistAdjointComparison_h0
      (rightAdj := P.rightAdj) P.leftAdj P.cotwistCone)

namespace AdjointComparisonConditions

variable {P : EnhancedAdjunctionCones S L R} [IsPretriangulated B]
  (h : AdjointComparisonConditions P)

/-- The canonical twist-side comparison, packaged as Mathlib's selected
isomorphism. -/
noncomputable def twistIso :
    ((P.twistFunctor.shiftedFunctor (-1 : ℤ)).comp L).h0 ≅ R.h0 := by
  letI := h.twist
  exact asIso (DGAdjunction.CounitConeData.twistAdjointComparison_h0
    (rightAdj := P.rightAdj) P.leftAdj P.twist)

/-- The canonical cotwist-side comparison, packaged as Mathlib's selected
isomorphism. -/
noncomputable def cotwistIso :
    R.h0 ≅ (L.comp P.cotwistConeFunctor).h0 := by
  letI := h.cotwist
  exact asIso (DGAdjunction.UnitConeData.cotwistAdjointComparison_h0
    (rightAdj := P.rightAdj) P.leftAdj P.cotwistCone)

end AdjointComparisonConditions

end CategoryTheory.Triangulated.SphericalTwist
