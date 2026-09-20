/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.BoundedCoherent
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeProposition315
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Amplitude

/-!
# Finite amplitude and the bounded-coherent restriction after base change

`BaseChangeDecomposition.lean` leaves the bounded-coherent restriction of a
base-change decomposition as the pair of obligations `DecompositionData.BoundedData`
records: the chosen quasicoherent projectors preserve the intrinsic
bounded-coherent locus, and the restricted components generate it. This file
splits the first obligation along the decomposition of that locus and
discharges the half that is formal.

The locus is `schemeBoundedQuasicoherent ⊓ schemeFinitePresentationCohomology`
(`Dqc/BoundedCoherent.lean`). Preservation of the first conjunct follows from
a cohomological amplitude bound on the projectors and from nothing else, by
`RightProjectionData.HasFiniteCohomologicalAmplitude.preserves_bounded`.
Preservation of the second does not follow from any amplitude bound: finite
presentation of the cohomology sheaves of a projected object is a genuine
coherence statement about the geometry, so `PreservesCoherentCohomology`
stays an input, as does generation of the restricted locus.

Amplitude is measured against a t-structure on `Dqc(X_T)`. The repository has
no such t-structure -- boundedness in `Dqc(X_T)` is measured through the
inclusion by the canonical t-structure of the ambient all-sheaf derived
category -- so `TargetBoundedTStructure` carries one together with the only
property of it the argument uses: that its bounded objects are the ambiently
bounded ones. Supplying that structure is a geometric obligation, and it is
deliberately not the base-changed t-structure of a source t-structure, which
belongs to a separate lane.

Nothing here asserts finite amplitude for any projector, or constructs a
t-structure on `Dqc(X_T)`.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

universe u w

variable {S : Scheme.{u}}

/-- A t-structure on `Dqc(X_T)` that presents the ambient bounded locus.

`bounded_iff` is the whole interface: it says that the `t`-bounded objects of
this t-structure are exactly those whose underlying complex is bounded for the
canonical t-structure of the all-sheaf derived category, which is how
`Dqc.schemeBoundedQuasicoherent` is defined. No compatibility with pullback,
pushforward, or a source t-structure is asserted or used.

The pair is what keeps this non-vacuous. Amplitude against an arbitrary
t-structure would say nothing about the locus `BoundedData` cares about, and a
t-structure so coarse that every object is bounded would make amplitude cheap
-- but then `bounded_iff` would assert that every object of `Dqc(X_T)` has
bounded cohomology, which is false. What a consumer gains by choosing the
t-structure is only the freedom to prove amplitude in whichever presentation is
convenient. -/
structure TargetBoundedTStructure (X T : SchemeBaseChange S) where
  /-- A t-structure on the quasicoherent fibre category. -/
  tStructure : TStructure (TargetDqc X T)
  /-- Its bounded objects are exactly the ambiently bounded ones. -/
  bounded_iff (E : TargetDqc X T) :
    tStructure.bounded E ↔ Dqc.schemeBoundedQuasicoherent (X ⨯ T).left E

namespace DerivedBaseChangeData

variable {X T : SchemeBaseChange S} {D : DerivedBaseChangeData X T}
  {ι : Type w} [Preorder ι]
  {A : SemiorthogonalSequence (SourceDqc X) ι}
  {hcompact : D.PreservesCompactObjects}
  {horth : D.PerfectComponentsSemiorthogonal A}

namespace DecompositionData

variable (B : D.DecompositionData A hcompact horth)

/-- The chosen quasicoherent projectors have finite cohomological amplitude
for a presenting t-structure. The interval may depend on the component. -/
def HasFiniteAmplitude (τ : TargetBoundedTStructure X T) : Prop :=
  (quasicoherentProjections B).HasFiniteCohomologicalAmplitude τ.tStructure

/-- The chosen quasicoherent projectors preserve finite presentation of every
cohomology sheaf.

This is the coherence half of the bounded restriction and is left as an
explicit input: it is a finiteness statement about projected objects, and no
amplitude bound implies it. -/
def PreservesCoherentCohomology : Prop :=
  (quasicoherentProjections B).Preserves
    (Dqc.schemeFinitePresentationCohomology (X ⨯ T).left)

/-- Finite amplitude preserves ambient boundedness. This is the formal half of
the bounded restriction. -/
theorem preservesBoundedQuasicoherent {τ : TargetBoundedTStructure X T}
    (h : B.HasFiniteAmplitude τ) :
    (quasicoherentProjections B).Preserves
      (Dqc.schemeBoundedQuasicoherent (X ⨯ T).left) :=
  SemiorthogonalSequence.RightProjectionData.Preserves.of_iff τ.bounded_iff
    (SemiorthogonalSequence.RightProjectionData.HasFiniteCohomologicalAmplitude.preserves_bounded
      h)

/-- Finite amplitude and coherence preservation together discharge the
preservation obligation of `BoundedData`. -/
theorem projectionsPreserveBounded {τ : TargetBoundedTStructure X T}
    (h : B.HasFiniteAmplitude τ) (hcoh : B.PreservesCoherentCohomology) :
    (quasicoherentProjections B).Preserves
      (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left) :=
  SemiorthogonalSequence.RightProjectionData.Preserves.of_iff
    (fun E ↦ (Dqc.schemeBoundedCoherentCohomology_iff (X ⨯ T).left E).symm)
    ((B.preservesBoundedQuasicoherent h).inf hcoh)

/-- Assemble the bounded-coherent restriction from finite amplitude, coherence
preservation, and generation of the restricted locus. -/
theorem toBoundedData
    [(Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated]
    {τ : TargetBoundedTStructure X T}
    (h : B.HasFiniteAmplitude τ) (hcoh : B.PreservesCoherentCohomology)
    (hfull : (D.boundedSequence A hcompact horth).IsFull) :
    B.BoundedData :=
  { projectionsPreserveBounded := B.projectionsPreserveBounded h hcoh
    full := hfull }

/-- The bounded-coherent base-change sequence is strong as soon as the
quasicoherent projectors have finite amplitude and preserve coherence. -/
theorem boundedSequence_isStrong
    [(Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated]
    {τ : TargetBoundedTStructure X T}
    (h : B.HasFiniteAmplitude τ) (hcoh : B.PreservesCoherentCohomology)
    (hfull : (D.boundedSequence A hcompact horth).IsFull) :
    (D.boundedSequence A hcompact horth).IsStrong :=
  BoundedData.isStrong B (B.toBoundedData h hcoh hfull)

end DecompositionData

end DerivedBaseChangeData

namespace KFlatBaseChangeData

variable {X T : SchemeBaseChange S} {D : KFlatBaseChangeData X T}
  {ι : Type w} [Preorder ι]
  {A : SemiorthogonalSequence (SourceDqc X) ι}
  {hcompact : D.PreservesCompactObjects}
  {horth : D.toDerivedBaseChangeData.PerfectComponentsSemiorthogonal A}

namespace Proposition315CoreData

variable {P : D.SourceTensorData} {BP : KFlatBasePullbackData X}
  (C : D.Proposition315CoreData A P BP hcompact)

/-- The bounded-coherent restriction of the Proposition 3.15 decomposition
whose projectors were constructed from compact-generator approximations.

Everything categorical has already been discharged: semiorthogonality,
generation of the perfect and quasicoherent sequences, the projectors
themselves, and now preservation of boundedness. What is still supplied here
is exactly the geometry that no formal step produces -- a presenting
t-structure, finite amplitude against it, coherence preservation, and
generation of the bounded locus. -/
theorem toBoundedData
    [(Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated]
    (R : D.Proposition315ProjectionConstructionData C)
    {τ : TargetBoundedTStructure X T}
    (h : (C.toDecompositionDataOfProjectionConstruction R).HasFiniteAmplitude τ)
    (hcoh :
      (C.toDecompositionDataOfProjectionConstruction R).PreservesCoherentCohomology)
    (hfull : (D.toDerivedBaseChangeData.boundedSequence A
      (D.toDerivedPreservesCompactObjects hcompact)
      C.semiorthogonality.perfectSemiorthogonal).IsFull) :
    (C.toDecompositionDataOfProjectionConstruction R).BoundedData :=
  DerivedBaseChangeData.DecompositionData.toBoundedData _ h hcoh hfull

/-- Proposition 3.15 restricted to the bounded-coherent locus: the bounded
sequence is a strong semiorthogonal sequence. -/
theorem boundedSequence_isStrong
    [(Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated]
    (R : D.Proposition315ProjectionConstructionData C)
    {τ : TargetBoundedTStructure X T}
    (h : (C.toDecompositionDataOfProjectionConstruction R).HasFiniteAmplitude τ)
    (hcoh :
      (C.toDecompositionDataOfProjectionConstruction R).PreservesCoherentCohomology)
    (hfull : (D.toDerivedBaseChangeData.boundedSequence A
      (D.toDerivedPreservesCompactObjects hcompact)
      C.semiorthogonality.perfectSemiorthogonal).IsFull) :
    (D.toDerivedBaseChangeData.boundedSequence A
      (D.toDerivedPreservesCompactObjects hcompact)
      C.semiorthogonality.perfectSemiorthogonal).IsStrong :=
  DerivedBaseChangeData.DecompositionData.boundedSequence_isStrong _ h hcoh hfull

end Proposition315CoreData

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
