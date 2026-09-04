/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc

/-!
# Consuming the bounded-coherent and compact/perfect comparison hypotheses

`Dqc.lean` records two geometric identifications that are not available for an
arbitrary scheme at the current Mathlib pin:

* `Dᵇ(Coh X)` with the bounded coherent-cohomology locus in `Dqc(X)`;
* the perfect thick envelope with the compact objects of `Dqc(X)`.

Those statements remain explicit propositions with no global inhabitants.
This file is their consumer API: after a caller supplies the relevant
evidence, it extracts a coherent representative and exposes the corresponding
perfect/compact membership theorem. No instance is installed, so unsupported
schemes cannot acquire either identification through typeclass search.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.DerivedCategory

noncomputable section

universe u

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- Chosen bounded-coherent comparison data, extracted only from explicit
evidence that the comparison exists. -/
noncomputable def boundedCoherentDqcIdentification
    (h : HasBoundedCoherentDqcIdentification X) :
    BoundedCoherentDqcIdentification X :=
  Classical.choice h

/-- The concrete functor `Dᵇ(Coh X) ⥤ Dᵇ_coh(Dqc X)` is essentially
surjective once the bounded-coherent identification is supplied. -/
theorem boundedCoherentDerivedToDqc_essSurj
    (h : HasBoundedCoherentDqcIdentification X) :
    (boundedCoherentDerivedToDqc X).EssSurj := by
  let I := boundedCoherentDqcIdentification X h
  letI : I.equivalence.functor.EssSurj := inferInstance
  exact Functor.essSurj_of_iso I.comparison

/-- A chosen `Dᵇ(Coh X)` representative of a bounded coherent object of
`Dqc(X)`, conditional on the explicit comparison evidence. -/
noncomputable def boundedCoherentRepresentative
    (h : HasBoundedCoherentDqcIdentification X)
    (E : SchemeBoundedCoherentDqcCategory X) :
    SchemeBoundedCoherentDerivedCategory X :=
  (boundedCoherentDqcIdentification X h).equivalence.inverse.obj E

/-- The image of the chosen coherent representative is the original bounded
coherent `Dqc(X)` object. -/
noncomputable def boundedCoherentRepresentativeIso
    (h : HasBoundedCoherentDqcIdentification X)
    (E : SchemeBoundedCoherentDqcCategory X) :
    (boundedCoherentDerivedToDqc X).obj
        (boundedCoherentRepresentative X h E) ≅ E :=
  let I := boundedCoherentDqcIdentification X h
  (I.comparison.app (I.equivalence.inverse.obj E)).symm ≪≫
    I.equivalence.counitIso.app E

/-- Under the explicit compact/perfect comparison, membership in the
repository's perfect locus is exactly compactness in `Dqc(X)`. -/
theorem schemePerfectInDqc_iff_isCompact
    (h : PerfectObjectsAreCompactInDqc X)
    (E : SchemeQuasicoherentDerivedCategory X) :
    schemePerfectInDqc X E ↔ IsCompactObject.{0} E := by
  change schemePerfectInDqc X E ↔
    ObjectProperty.compactObjects.{0} E
  rw [h]

end

end AlgebraicGeometry.DerivedCategory.Dqc
