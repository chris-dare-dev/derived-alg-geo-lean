/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionComparison
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
    (DGAdjunction.CounitConeData.twistAdjointComparisonH0
      (rightAdj := P.rightAdj) P.leftAdj P.twist)
  /-- The canonical comparison `R ⟶ C L` is invertible on `H⁰`. -/
  cotwist : IsIso
    (DGAdjunction.UnitConeData.cotwistAdjointComparisonH0
      (rightAdj := P.rightAdj) P.leftAdj P.cotwistCone)

namespace AdjointComparisonConditions

variable {P : EnhancedAdjunctionCones S L R} [IsPretriangulated B]
  (h : AdjointComparisonConditions P)

/-- The canonical twist-side comparison, packaged as Mathlib's selected
isomorphism. -/
noncomputable def twistIso :
    ((P.twistFunctor.shiftedFunctor (-1 : ℤ)).comp L).h0 ≅ R.h0 := by
  letI := h.twist
  exact asIso (DGAdjunction.CounitConeData.twistAdjointComparisonH0
    (rightAdj := P.rightAdj) P.leftAdj P.twist)

/-- The canonical cotwist-side comparison, packaged as Mathlib's selected
isomorphism. -/
noncomputable def cotwistIso :
    R.h0 ≅ (L.comp P.cotwistConeFunctor).h0 := by
  letI := h.cotwist
  exact asIso (DGAdjunction.UnitConeData.cotwistAdjointComparisonH0
    (rightAdj := P.rightAdj) P.leftAdj P.cotwistCone)

section ShiftedCotwist

variable [IsPretriangulated A]

/-- The cotwist comparison in Anno--Logvinenko's conventional shifted form
`R ≅ (F L)[1]`, where `F = C[-1]`.

The final isomorphism is Mathlib's opposite-shift cancellation for the
`HasShift` structure on closed dg functors. -/
noncomputable def cotwistShiftedIso :
    R.h0 ≅
      ((L.comp P.cotwistFunctor).shiftedFunctor 1).h0 :=
  h.cotwistIso ≪≫
    (DGFunctor.shiftedFunctorCompIsoIdH0
      (L.comp P.cotwistConeFunctor) (-1 : ℤ) 1 (by omega)).symm

/-- The hom of `cotwistShiftedIso` is the canonical shifted-target comparison,
not an independently chosen natural isomorphism. -/
@[simp]
theorem cotwistShiftedIso_hom :
    h.cotwistShiftedIso.hom =
      DGAdjunction.UnitConeData.cotwistAdjointComparisonShiftedH0
        (rightAdj := P.rightAdj) P.leftAdj P.cotwistCone :=
  rfl

end ShiftedCotwist

end AdjointComparisonConditions

end CategoryTheory.Triangulated.SphericalTwist
