# Tasks

## 1. Plan and loop-controller readiness

- [ ] 1.1 Add `eligibility.allow_epic_issues` as an explicit, subset-checked manifest field and preserve rejection of every unlisted `epic`, `blocked`, `research`, or `type:spike` issue; verify with `python -m unittest discover -s scripts/tests -p "test_*.py"`.
- [ ] 1.2 Add the three-issue SF11 manifest with exact issue dependencies, frozen chunk file prefixes, four reviewers, `max_review_rounds_per_chunk: 3`, targeted-check requirements, and explicit epic opt-in; verify with `python scripts/loop_engine.py validate --spec .claude/loop-specs/sf11-pilot.yaml`.
- [ ] 1.3 Record stale comments, roadmap mismatches, branch/base friction, and time-wasting build practices in `notes/loop-engineering-sf11.md`; verify the note names each observation's file and does not claim an unproved theorem.
- [ ] 1.4 Validate the proposal, delta spec, design, and task checklist with `openspec validate sf11-base-change-t-structures --strict --no-interactive` and `openspec validate --all --strict --no-interactive`.

## 2. Issue #1060 — constructed base-change categories

- [ ] 2.1 Replace the remaining supplied K-flat tensor/pullback and compactness seams in the frozen Families scope with source-faithful geometric constructions or explicit theorem hypotheses; verify the affected modules compile and the axiom/no-sorry audit reports no new evidence.
- [ ] 2.2 Prove the concrete external-product semiorthogonality, fullness, linearity, projection-formula, generation, approximation, truncation-cocontinuity, compact-intersection, and compact-preservation obligations used by Proposition 3.15 and Theorem 3.17; verify with targeted `lake build` commands for only the changed Families modules.
- [ ] 2.3 Construct the bounded-coherent preservation and finite-amplitude data needed by the selected theorem hypotheses, then prove the pullback/pushforward functors and Lemma 3.18 equivalences through the existing inclusion comparison maps; verify with the targeted base-change functor build and `python scripts/precheck.py --help`-compatible repository checks.
- [ ] 2.4 Run the four independent adversarial reviews for the frozen #1060 commit, record them in `.loop-runs`, and adjudicate only after all findings are resolved or the third round is terminal; verify the ledger has exactly one reviewed commit per round and never a fourth round.

## 3. Issue #1061 — S-local t-structures and slicings

- [ ] 3.1 Complete the S-local quantifier and uniqueness API over quasi-compact opens, then provide two distinct affine-base inhabitants using actual base-change and t-exactness data; verify with a targeted build of `Families/SLocal.lean` and its direct consumers.
- [ ] 3.2 Prove the noetherian-locality statement of Lemma 4.15 and filtration-lifting statement of Lemma 4.16(3), retaining the paper's hypotheses at the call site; verify with focused theorem tests and no new axioms.
- [ ] 3.3 Add the S-local slicing analogue using the existing phase/slicing ownership and prove its restriction and uniqueness compatibility; verify with the smallest changed Stability/Phase module build.
- [ ] 3.4 Run the four independent adversarial reviews for the frozen #1061 commit, record them in `.loop-runs`, and adjudicate under the same three-round cap; verify the ledger blocks any fourth attempt.

## 4. Issue #1062 — Theorem 5.3 on `(Dqc)_T`

- [ ] 4.1 Reconcile `TStructure.IndExtensionData` with the Ind/filtered-colimit presentation of Lemma 5.1 through comparison theorems, without adding a second carrier; verify by compiling the existing Ind-extension module plus the new bridge module.
- [ ] 4.2 Prove the affine closure, filtered-colimit truncation, flat/fpqc descent formulas, tensor right t-exactness, and four t-exactness clauses of Theorem 5.3 for the supported base-change hypotheses; verify with targeted builds only for the changed theorem modules.
- [ ] 4.3 Run the four independent adversarial reviews for the frozen #1062 commit, record them in `.loop-runs`, and adjudicate under the same three-round cap; verify all reviews point to the exact final commit.

## 5. Integration and controlled completion

- [ ] 5.1 Run `scripts/precheck.sh` with only the targeted Lean module selection for each changed chunk, plus the no-sorry, layering, style, roadmap, and trust-surface checks; verify that no full-repository build command is invoked locally.
- [ ] 5.2 Push, create, approve, and merge each PR only through the enabled loop controller, refreshing the protected base between dependent issues; verify each action is bound to the reviewed head and required checks.
- [ ] 5.3 Close #1060, #1061, and #1062 only after the controller confirms their merged PR closing keywords; verify the final issue states and OpenSpec task completion agree with the three passing ledgers.
