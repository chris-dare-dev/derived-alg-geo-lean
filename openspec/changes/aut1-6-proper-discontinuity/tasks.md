# Tasks

## 1. Reconcile the existing implementation

- [ ] 1.1 Audit the existing proper-discontinuity module against every requirement, tighten its explanatory boundary if needed, and verify that no inhabitant, unrestricted covering theorem, chamber-stabilizer theorem, `sorry`, `admit`, or bypass axiom is introduced
- [ ] 1.2 Confirm the PhaseTopology audit lists the data structure, its projections, and every public consequence, and verify the audit remains append-only in its proper-discontinuity section

## 2. Repair repository guidance

- [ ] 2.1 Update the cutover ledger so it no longer says #927 has no implemented portion while preserving the distinction between this capability and the unrelated cutover row
- [ ] 2.2 Record verified tracker inconsistencies and agent time-wasters in the loop-engineering note, including the stale blocked label, the non-default stacked-PR closure behavior, Windows cache seeding friction, and stale command guidance

## 3. Validate the bounded chunk

- [ ] 3.1 Run `openspec validate --all --strict --no-interactive` and `python scripts/loop_engine.py validate --spec .claude/loop-specs/aut1-6-proper-discontinuity.yaml`
- [ ] 3.2 Run one named Lean target with `LEAN_NUM_THREADS=2` for `DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.ProperDiscontinuity`, and run `SKIP_ACTIONLINT=1 bash scripts/precheck.sh --no-build` because the local actionlint dependency is absent; do not invoke the whole-repository build
- [ ] 3.3 Re-run the focused repository audits for forbidden proof escapes, duplicate canonical roots, unrestricted covering claims, and out-of-scope changed files; record the exact commit for the four-reviewer panel

## 4. Complete the bounded loop

- [ ] 4.1 Initialize the digest-bound ledger and obtain independent mathematics, repository-boundary, abstraction, and mathlib review verdicts on the same commit
- [ ] 4.2 Apply only recorded findings, never exceeding three review/improve rounds for this frozen chunk, then adjudicate the passing ledger
- [ ] 4.3 Use the controller for the authorized issue comment, push, PR creation, approval, merge, and final issue closure, and verify the merged PR closes #927 before archiving this OpenSpec change
