/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeSequence
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.Projection

/-!
# Constructing projections for scheme base change

This file packages the projection step of Proposition 3.15 of
arXiv:1902.08184.

For each source component, compact-generator approximation data construct a
chosen right projection from `Dqc(X_T)` onto the corresponding coproduct
closure.  If those ambient projectors preserve compact objects, they restrict
to the compact-object carrier.  An explicit compact-intersection equality
then identifies the restricted component with the perfect base-change
component.

The two geometric inputs which are not formal are visible in the interfaces:
continuity of the compactly generated truncations, and the identification of
compact objects in the coproduct closure with the perfect envelope.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
  AlgebraicGeometry

universe u w

namespace KFlatBaseChangeData

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  (D : KFlatBaseChangeData X T)
  {ι : Type w} [Preorder ι]
  (A : SemiorthogonalSequence (SourceDqc X) ι)

/-- Componentwise compact-generator approximations for the perfect envelopes.
Their zero aisles are definitionally the quasicoherent base-change
components. -/
structure QuasicoherentProjectionApproximationData : Prop where
  /-- Brown-style approximation data for each perfect envelope. -/
  componentApproximation (i : ι) :
    TStructure.CompactGeneratorApproximation.{u}
      (D.perfectEnvelope (A.component i))

namespace QuasicoherentProjectionApproximationData

variable {D A}
  (B : D.QuasicoherentProjectionApproximationData A)
include B

/-- Assemble the componentwise compactly generated projections into chosen
projection data for the quasicoherent sequence. -/
noncomputable def quasicoherentProjections
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A) :
    (D.quasicoherentSequence A hcompact horth).RightProjectionData where
  componentProjection i := (B.componentApproximation i).rightProjectionData

/-- Continuity of the component truncations gives continuity of every
quasicoherent ambient projector. -/
theorem quasicoherentProjectionCocontinuous
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A)
    (htrunc : ∀ i, Functor.PreservesSmallCoproducts.{u}
      ((B.componentApproximation i).tStructure.truncLE 0)) :
    ∀ i, Functor.PreservesSmallCoproducts.{u}
      ((B.quasicoherentProjections hcompact horth).ambientProjection i) :=
  fun i ↦ (B.componentApproximation i).rightProjectionData_preservesSmallCoproducts
    (htrunc i)

/-- The constructed quasicoherent projections prove strongness once the
source components are triangulated. -/
theorem quasicoherentIsStrong
    (hA : A.HasTriangulatedComponents)
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A) :
    (D.quasicoherentSequence A hcompact horth).IsStrong :=
  fun i ↦ ObjectProperty.RightProjectionData.isRightAdmissible
    ((B.quasicoherentProjections hcompact horth).componentProjection i)
      (D.quasicoherentSequence_hasTriangulatedComponents A hA hcompact horth i)

end QuasicoherentProjectionApproximationData

/-- Data identifying the compact restriction of chosen quasicoherent
projectors with the perfect base-change sequence. -/
structure PerfectProjectionRestrictionData
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A)
    (Q : (D.quasicoherentSequence A hcompact horth).RightProjectionData) : Prop where
  /-- Each ambient quasicoherent projector preserves compact objects. -/
  projectionPreservesCompact (i : ι) :
    ObjectProperty.compactObjects.{u} ≤
      (ObjectProperty.compactObjects.{u}).inverseImage
        (Q.ambientProjection i)
  /-- The compact objects in a quasicoherent component are exactly its
  perfect-envelope component. -/
  compactIntersection (i : ι) :
    ((D.quasicoherentSequence A hcompact horth).component i).inverseImage
        (targetPerfectToDqc X T) =
      (D.perfectCategorySequence A horth).component i

namespace PerfectProjectionRestrictionData

variable {D A hcompact horth Q}
  (B : D.PerfectProjectionRestrictionData A hcompact horth Q)
include B

/-- Restrict the quasicoherent projectors to compact objects and identify the
result with the perfect base-change components. -/
def perfectProjections :
    (D.perfectCategorySequence A horth).RightProjectionData where
  componentProjection i :=
    ((Q.componentProjection i).restrict
      (B.projectionPreservesCompact i)).ofEq (B.compactIntersection i)

/-- Compact restriction proves strongness of the perfect sequence when the
source components are triangulated. -/
theorem perfectIsStrong (hA : A.HasTriangulatedComponents) :
    (D.perfectCategorySequence A horth).IsStrong :=
  fun i ↦ ((perfectProjections B).componentProjection i).isRightAdmissible
    (D.perfectCategorySequence_hasTriangulatedComponents A hA horth i)

end PerfectProjectionRestrictionData

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
