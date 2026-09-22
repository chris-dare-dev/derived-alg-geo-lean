# Tasks

## 1. Plan and loop-controller readiness

- [x] 1.1 Add `eligibility.allow_epic_issues` as an explicit, subset-checked manifest field and preserve rejection of every unlisted `epic`, `blocked`, `research`, or `type:spike` issue; verify with `python -m unittest discover -s scripts/tests -p "test_*.py"`.
- [x] 1.2 Add the three-issue SF11 manifest with exact issue dependencies, frozen chunk file prefixes, four reviewers, `max_review_rounds_per_chunk: 5`, targeted-check requirements, and explicit epic opt-in; verify with `python scripts/loop_engine.py validate --spec .claude/loop-specs/sf11-pilot.yaml`.
- [x] 1.3 Record stale comments, roadmap mismatches, branch/base friction, and time-wasting build practices in `notes/loop-engineering-sf11.md`; verify the note names each observation's file and does not claim an unproved theorem.
- [x] 1.4 Validate the proposal, delta spec, design, and task checklist with `openspec validate sf11-base-change-t-structures --strict --no-interactive` and `openspec validate --all --strict --no-interactive`.

## 2. Issue #1060 — constructed base-change categories

- [x] 2.1 Replace the supplied K-flat tensor/pullback seams in the frozen Families scope with source-faithful producers and route compactness through named theorem hypotheses at the operation owner; verify the affected modules compile and the axiom/no-sorry audit reports no new evidence.
- [x] 2.2 Prove the formal external-product semiorthogonality, linearity, projection-formula, closure, restriction, and Lemma 3.18 mechanisms used by Proposition 3.15 and Theorem 3.17. Keep tensor duality, fullness/generation, projection approximation/restriction, and compact-preservation as explicit named geometric inputs where the repository has no theorem; verify with targeted `lake build` commands for only the changed Families modules.
- [x] 2.3 Construct the bounded/coherent restriction and finite-amplitude adapters, then prove the pullback/pushforward functors and detection equivalences through the existing inclusion comparison maps. Keep bounded coherence, finite amplitude, target t-structure, and component detection as explicit geometry-owner hypotheses; verify with `scripts/precheck.sh --no-build` plus `LEAN_NUM_THREADS=2 lake build DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.IndExtension`.
- [x] 2.4 Run the four independent adversarial reviews for the frozen #1060 commit, record them in `.loop-runs`, and adjudicate only after all findings are resolved or the fifth round is terminal; verify the ledger has exactly one reviewed commit per round and never a sixth round.

## 3. Issue #1061 — S-local t-structures and slicings

- [x] 3.1 Complete the S-local quantifier and uniqueness API over quasi-compact opens, then provide an affine witness adapter consuming actual base-change and t-exactness data; verify with targeted builds of `Families/SLocal.lean` and its direct consumers.
- [x] 3.2 Provide theorem-backed formal adapters for the noetherian-locality statement of Lemma 4.15 and filtration-lifting statement of Lemma 4.16(3), retaining the paper's geometric hypotheses at the owner call site; verify with focused theorem tests and no new axioms.
- [x] 3.3 Add the S-local slicing analogue in the geometry-owned stability subtree using the existing phase/slicing ownership, and prove its restriction and uniqueness compatibility; verify with the smallest changed Stability/Phase module build.
- [x] 3.4 Run the four independent adversarial reviews for the frozen #1061 commit, record them in `.loop-runs`, and adjudicate under the same five-round cap; verify the ledger blocks any sixth attempt.

## 4. Issue #1062 — Theorem 5.3 on `(Dqc)_T`

- [x] 4.1 Reconcile `TStructure.IndExtensionData` with the Ind/filtered-colimit presentation of Lemma 5.1 through the single bridge package; prove inclusion t-exactness and expose the existing aisle comparison without adding a second carrier. Verify by compiling the existing Ind-extension module and `IndFilteredColimits.lean`.
- [x] 4.2 Expose source-shaped owner boundaries for the filtered-colimit, flat/fpqc descent, tensor right t-exactness, and four t-exactness clauses of Theorem 5.3, and prove their formal range/exactness composition APIs. Keep the scheme-level geometry explicit; verify with targeted builds of only the changed theorem modules.
- [ ] 4.3 Run the four independent adversarial reviews for the frozen #1062 commit, record them in `.loop-runs`, and adjudicate under the same five-round cap; verify all reviews point to the exact final commit.

## 5. Integration and controlled completion

- [ ] 5.1 Run `scripts/precheck.sh` with only the targeted Lean module selection for each changed chunk, plus the no-sorry, layering, style, roadmap, and trust-surface checks; verify that no full-repository build command is invoked locally.
- [ ] 5.2 Push, create, approve, and merge each PR only through the enabled loop controller, refreshing the protected base between dependent issues; verify each action is bound to the reviewed head and required checks.
- [ ] 5.3 Close #1060, #1061, and #1062 only after the controller confirms their merged PR closing keywords; verify the final issue states and OpenSpec task completion agree with the three passing ledgers.

## 6. Follow-up issue #1445 — repair the merged SF11.3 boundary

The original #1062 task remains historical: its PR merged with a failed CI
audit and without a locally recoverable ledger. This section is a fresh,
five-round-bounded follow-up and does not retroactively mark task 4.3 complete.

- [ ] 6.1 Remove projection-only or duplicate carriers from the filtered-colimit and Theorem 5.3 boundary, reusing canonical `IndExtensionData` and Mathlib exactness interfaces or proving substantive comparison theorems.
- [ ] 6.2 Split one-sided exactness from genuinely t-exact clauses and make the tensor, range-descent, and local-comparison owner inputs source-shaped without claiming unproved scheme-level geometry.
- [ ] 6.3 Add the actual AlgebraicGeometry declarations reported by CI to their proper audit slices; do not modify `scripts/audit_missing_baseline.txt` or raise a ceiling.
- [ ] 6.4 Run the four independent adversarial reviewers on one frozen final commit, record verbatim outputs in a digest-bound ledger, and stop after the fifth unsuccessful round.
- [ ] 6.5 Run the required CI/trust checks and use the loop controller for the guarded PR handoff and closure of #1445.
