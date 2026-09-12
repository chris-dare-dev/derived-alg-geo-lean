/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeSequence

/-!
# Decomposition data for base-changed sequences

The sequence constructors isolate semiorthogonality formally. This file
packages the remaining geometric content of Proposition 3.15 of
arXiv:1902.08184: generation, admissible component projections, and
cocontinuity of the `Dqc` projections.

No field is manufactured from the K-flat construction. In particular,
fullness and right adjoints remain explicit obligations. Once supplied, the
generic projection API turns the chosen adjoints into paper-strong
semiorthogonal decompositions.

For the bounded-coherent restriction, triangulatedness of the intrinsic
bounded-coherent locus is an explicit typeclass hypothesis. This is essential
over a non-Noetherian scheme: finite-presentation cohomology is not closed
under cones without additional geometry.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

universe u w

namespace KFlatBaseChangeData

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  (D : KFlatBaseChangeData X T)
  {ι : Type w} [Preorder ι]
  (A : SemiorthogonalSequence (SourceDqc X) ι)
  (hcompact : D.PreservesCompactObjects)
  (horth : D.PerfectComponentsSemiorthogonal A)

/-- The remaining geometric data making the perfect and quasicoherent
base-change sequences into full strong decompositions. -/
structure DecompositionData where
  /-- Each source component is triangulated. The corresponding perfect and
  quasicoherent base-change components are then triangulated formally. -/
  sourceComponentsTriangulated : A.HasTriangulatedComponents
  /-- The perfect components generate the compact-object carrier. -/
  perfectFull : (D.perfectCategorySequence A horth).IsFull
  /-- Chosen right projections onto all perfect components. -/
  perfectProjections :
    (D.perfectCategorySequence A horth).RightProjectionData
  /-- The quasicoherent components generate `Dqc(X_T)`. -/
  quasicoherentFull :
    (D.quasicoherentSequence A hcompact horth).IsFull
  /-- Chosen right projections onto all quasicoherent components. -/
  quasicoherentProjections :
    (D.quasicoherentSequence A hcompact horth).RightProjectionData
  /-- The ambient `Dqc` projection endofunctors preserve all coproducts in
  the scheme universe. -/
  quasicoherentProjectionCocontinuous :
    ∀ i, (quasicoherentProjections.ambientProjection i).PreservesSmallCoproducts.{u}

namespace DecompositionData

variable {D A hcompact horth}
  (B : D.DecompositionData A hcompact horth)

include B

/-- The perfect-category sequence is strong in the paper's sense. -/
theorem perfectIsStrong :
    (D.perfectCategorySequence A horth).IsStrong :=
  fun i ↦ ((perfectProjections B).componentProjection i).isRightAdmissible
    (D.perfectCategorySequence_hasTriangulatedComponents A
      B.sourceComponentsTriangulated horth i)

/-- The quasicoherent sequence is strong in the paper's sense. -/
theorem quasicoherentIsStrong :
    (D.quasicoherentSequence A hcompact horth).IsStrong :=
  fun i ↦ ((quasicoherentProjections B).componentProjection i).isRightAdmissible
    (D.quasicoherentSequence_hasTriangulatedComponents A
      B.sourceComponentsTriangulated hcompact horth i)

/-- The bounded-coherent object property on the fibre product. -/
abbrev boundedLocus : ObjectProperty (TargetDqc X T) :=
  Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left

/-- Additional data needed to restrict the quasicoherent decomposition to
the bounded-coherent locus. -/
structure BoundedData
    [(boundedLocus (X := X) (T := T)).IsTriangulated] where
  /-- Every quasicoherent projector preserves bounded coherent cohomology. -/
  projectionsPreserveBounded :
    (quasicoherentProjections B).Preserves
      (boundedLocus (X := X) (T := T))
  /-- The restricted components generate the bounded-coherent carrier. -/
  full : (D.boundedSequence A hcompact horth).IsFull

namespace BoundedData

variable [(boundedLocus (X := X) (T := T)).IsTriangulated]
  (BB : B.BoundedData)

include BB

/-- The chosen component projections restricted to bounded coherent
cohomology. -/
def projections :
    (D.boundedSequence A hcompact horth).RightProjectionData :=
  (quasicoherentProjections B).restrict
    (boundedLocus (X := X) (T := T))
    BB.projectionsPreserveBounded

/-- The bounded sequence is strong once the quasicoherent projectors preserve
bounded coherent cohomology. -/
theorem isStrong : (D.boundedSequence A hcompact horth).IsStrong := by
  simpa [KFlatBaseChangeData.boundedSequence, boundedLocus] using
    (quasicoherentProjections B).inverseImage_isStrong
      (boundedLocus (X := X) (T := T))
      (D.quasicoherentSequence_hasTriangulatedComponents A
        B.sourceComponentsTriangulated hcompact horth)
      (fun i ↦ D.quasicoherentComponent_isClosedUnderIsomorphisms
        (A.component i))
      BB.projectionsPreserveBounded

end BoundedData

end DecompositionData

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
