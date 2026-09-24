/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc

/-!
# Splitting the intrinsic bounded-coherent locus

`Dqc.schemeBoundedCoherentCohomology X` is a conjunction: ambient boundedness
of the underlying complex, and finite presentation of every cohomology sheaf.
`Dqc.lean` writes both conjuncts into one definition. This file names the
second on its own and records the resulting decomposition.

The split is worth making because the two halves are preserved for different
reasons. Boundedness of `F.obj E` follows formally from a cohomological
amplitude bound on `F`, with no finiteness hypothesis anywhere; finite
presentation of the cohomology sheaves of `F.obj E` follows from no amplitude
bound at all and is a genuine geometric input. Naming the conjuncts separately
lets a consumer discharge the first and assume only the second.

On a locally Noetherian scheme, finite-presentation module sheaves form a
weak Serre class. Both halves therefore cut out triangulated subcategories
of `Dqc(X)`, as does their intersection. This gives the intrinsic bounded-
coherent locus the triangulated structure needed to restrict later
base-change constructions; it does not construct a base-changed t-structure.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated
open AlgebraicGeometry.DerivedCategory

noncomputable section

universe u

variable (X : Scheme.{u})

/-- Finite presentation of every cohomology sheaf of an object of `Dqc(X)`.
This is the coherence half of `schemeBoundedCoherentCohomology`; on its own it
asserts nothing about boundedness. -/
def schemeFinitePresentationCohomology :
    ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦ ∀ n : ℤ, (SheafOfModules.isFinitePresentation X.ringCatSheaf)
    ((DerivedCategory.homologyFunctor X.Modules n).obj E.obj)

/-- Membership in the intrinsic bounded-coherent locus is ambient boundedness
together with finite presentation of every cohomology sheaf. -/
theorem schemeBoundedCoherentCohomology_iff
    (E : SchemeQuasicoherentDerivedCategory X) :
    schemeBoundedCoherentCohomology X E ↔
      schemeBoundedQuasicoherent X E ∧
        schemeFinitePresentationCohomology X E :=
  Iff.rfl

/-- The intrinsic bounded-coherent locus is the meet of its two conjuncts. -/
theorem schemeBoundedCoherentCohomology_eq_inf :
    schemeBoundedCoherentCohomology X =
      schemeBoundedQuasicoherent X ⊓ schemeFinitePresentationCohomology X :=
  rfl

/-- Bounded coherent cohomology implies coherence of every cohomology sheaf. -/
theorem schemeBoundedCoherentCohomology_le_finitePresentationCohomology :
    schemeBoundedCoherentCohomology X ≤ schemeFinitePresentationCohomology X :=
  fun _ hE ↦ hE.2

instance : (schemeFinitePresentationCohomology X).IsClosedUnderIsomorphisms where
  of_iso e hE n :=
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor X.Modules n).mapIso
        ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e)) (hE n)

/-- Ambient cohomological boundedness is triangulated after restriction to
`Dqc(X)`, without a Noetherian hypothesis. -/
instance schemeBoundedQuasicoherent_isTriangulated :
    (schemeBoundedQuasicoherent X).IsTriangulated := by
  change ((DerivedCategory.TStructure.t (C := X.Modules)).bounded.inverseImage
    (SchemeQuasicoherentDerivedCategory.ι X)).IsTriangulated
  infer_instance

/-- On a locally Noetherian scheme, coherent module sheaves form a weak Serre
class, so having coherent cohomology is a triangulated condition on `Dqc(X)`. -/
instance schemeFinitePresentationCohomology_isTriangulated [IsLocallyNoetherian X] :
    (schemeFinitePresentationCohomology X).IsTriangulated := by
  change ((DerivedCategory.cohomologyIn (Scheme.coherent X)).inverseImage
    (SchemeQuasicoherentDerivedCategory.ι X)).IsTriangulated
  infer_instance

/-- The intrinsic bounded-coherent locus is triangulated on a locally
Noetherian scheme. This is a prerequisite for restricting a t-structure to
that locus, not a proof that its truncations preserve coherent cohomology. -/
instance schemeBoundedCoherentCohomology_isTriangulated [IsLocallyNoetherian X] :
    (schemeBoundedCoherentCohomology X).IsTriangulated := by
  rw [schemeBoundedCoherentCohomology_eq_inf]
  infer_instance

end

end AlgebraicGeometry.DerivedCategory.Dqc
