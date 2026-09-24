# Tasks

## 1. Issue #897 — Full faithfulness and the co-Serre condition

- [ ] 1.1 Add `CoSerreFunctorData`, prove full faithfulness of both duality functors under explicit Hom-finiteness, construct their adjunction, and derive the existing equivalence package from the co-Serre input; update the linear umbrella and `SerreFunctor` audit. Freeze this chunk to `CategoryTheory/Linear/SerreFunctor/Equivalence.lean`, `CategoryTheory/Linear/SerreFunctor.lean`, `scripts/StabilityConditionAudit/SerreFunctor.lean`, and `docs/architecture/generalization-backlog.md`. Verify with a named build of `DerivedAlgGeo.CategoryTheory.Linear.SerreFunctor`, the focused audit target, `scripts/check_layering.py`, and `scripts/check_umbrella_coverage.py`.

## 2. Issue #898 — Conjugation and shift consequences

- [ ] 2.1 Prove the conjugated Serre data and `transportIso` for a linear autoequivalence in the linear owner; export it from the linear umbrella. Freeze this chunk to `CategoryTheory/Linear/SerreFunctor/Transport.lean`, `CategoryTheory/Linear/SerreFunctor.lean`, and `scripts/StabilityConditionAudit/SerreFunctor.lean`. Verify with a named build of `DerivedAlgGeo.CategoryTheory.Linear.SerreFunctor` and its focused audit target.
- [ ] 2.2 Derive shift commutation from conjugation, prove `CommShift ℤ` coherence, discharge the supported triangulated/exactness and `TriEquiv` obligations, and prove `chiHom_symm`; make only the specified Euler-form disclaimer correction and update the triangulated umbrella and audit. Freeze this chunk to `CategoryTheory/Triangulated/SerreFunctor/Shift.lean`, `CategoryTheory/Triangulated/SerreFunctor.lean`, `CategoryTheory/Triangulated/GrothendieckGroup/EulerForm.lean`, and `scripts/StabilityConditionAudit/SerreFunctor.lean`. Verify with named builds of `DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor` and `DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm`, the focused audit target, and `scripts/check_umbrella_coverage.py`.

## 3. Issue #899 — Supplied geometric bridge

- [ ] 3.1 Add `GeometricSerreData` at the geometry owner with supplied duality and naturality fields, Hom-finiteness and bounded-range sheaf compatibility; project it one way to existing `SerreFunctorData`, state the supported surface/K3 recoveries, document the three uninhabitedness reasons, add only the import to the Serre umbrella, and register declarations in the geometry audit. Freeze this chunk to `AlgebraicGeometry/Duality/Serre/Categorical.lean`, `AlgebraicGeometry/Duality/Serre.lean`, and `scripts/AlgebraicGeometryAudit/SerreCategorical.lean`. Verify with named builds of `DerivedAlgGeo.AlgebraicGeometry.Duality.Serre` and `AlgebraicGeometryAudit`, plus `scripts/check_layering.py` and `scripts/check_umbrella_coverage.py`.

## 4. Batch completion

- [ ] 4.1 After all implementation chunks pass their independent reviews, run `scripts/precheck.sh`, check the audit-completeness and no-sorry gates, and obtain the required protected `ci` result for the exact candidate head; record each result in the loop ledger.
- [ ] 4.2 Require each source manifest to emit its controller attestation after its passing ledger and before merge. After each predecessor PR is merged and its issue is confirmed closed, re-read live dependencies and create the next one-issue successor manifest with the exact predecessor attestation, reviewed head, and merge commit; complete #898 and #899 only after their own complete PRs merge and confirm all three SRF1 issues are closed before archiving this OpenSpec change.
