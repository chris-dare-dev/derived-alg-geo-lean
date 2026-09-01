/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Equivariance
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.HN
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.Polishchuk

/-!
# The Polishchuk/Ind inducing boundary

Appendix A of arXiv:2607.28411v1 proves that a raw preimage collection is a
slicing only under substantial extra hypotheses.  In Theorem A.17 these
include compactly generated large categories, boundedness reflection, and
right t-exactness of the monad; Corollary A.23 uses the dual condition
`Phi PhiL(P(phi)) ⊆ P(≥ phi)`.  Propositions 3.3 and 3.8 then verify the
corresponding geometric conditions for finite and faithfully-flat morphisms.

The repository owns the large-category definitions of compact objects and
`Coprod`, the Brown approximation tower, A.13, the A.14 bounded restriction,
and the categorical Steps 1--4 of A.17; see
`CompactlyGenerated.Polishchuk`.  Its bounded phase-indexed output is
`Slicing.InducedTStructures`, and Corollary A.23's finite truncation argument
constructs `Slicing.PreimageData` from exactly that output in
`Phase.Transfer.HN`.

This module is intentionally only the import boundary joining those two owned
results.  The former global theorem-switch proposition and its bounded
left-adjoint shadow have been deleted:
geometric callers now provide the actual phase-indexed A.17 output, never a
global theorem switch or a preconstructed slicing witness.
-/
