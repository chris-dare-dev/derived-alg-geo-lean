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
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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

end

end AlgebraicGeometry.DerivedCategory.Dqc
