# Tasks

## 1. Provider identity and policy

- [x] 1.1 In `scripts/ci_github_evidence.py`, add a read-only GitHub client with bounded pagination, explicit response errors and injectable transport; verify multi-page, rate-limit, malformed-response and truncated-page cases in `scripts/tests/test_ci_github_evidence.py`.
- [x] 1.2 Resolve current `main`, PR base/head, primary workflow run/attempt and candidate commit/tree through the protected workflow's run artifact and immutable Git objects, then recheck moving identities; verify exact-candidate, moved-head/base, missing-artifact, changed-workflow and unproved-parent fixtures in `scripts/tests/test_ci_github_evidence.py`.
- [x] 1.3 Load `scripts/ci_gate_inventory.json` from the protected-base Git object and compare its required contexts and producers with live branch protection; verify PR-authored policy removal, unavailable protection and unknown required-context fixtures in `scripts/tests/test_ci_github_evidence.py`.

## 2. Observations and evidence

- [x] 2.1 Enumerate all PR-head check-suite pages, each suite's check-run pages and all PR-head commit-status pages while proving the separate merge candidate through the workflow artifact and Git parents; preserve provider IDs and distinct producers, and verify duplicate-name, mixed-status and incomplete-enumeration fixtures in `scripts/tests/test_ci_github_evidence.py`.
- [x] 2.2 Associate GitHub Actions jobs with the verified workflow run and attempt, retaining earlier attempts as non-authorizing observations; verify successful rerun and ambiguous-attempt fixtures in `scripts/tests/test_ci_github_evidence.py`.
- [x] 2.3 Read candidate pin blobs and emit canonical observation payloads, the protected inventory and live required-check protection snapshot with hashes of actual retained bytes; call `ci_contract.validate_evidence` with independently read anchors. Verify tampered payload, absent pin, optional-red and required-red fixtures using `python3 -m unittest discover -s scripts/tests -p 'test_ci_github_evidence.py'`.
- [x] 2.4 Add a read-only `scripts/loop_engine.py evidence` command that consumes collector/validator output without changing queue admission; verify a passing fixture and a denied fixture through the controller command in `scripts/tests/test_loop_engine.py`.
- [x] 2.5 In `scripts/ci_contract.py` and `scripts/ci_gate_inventory.json`, represent the optional runless GitHub Advanced Security check with its actual head subject and no invented workflow run; verify version 5 focused fixtures reject a fabricated run and accept a genuine head-bound check.
- [x] 2.6 Normalize applicable auxiliary check-app observations in `scripts/ci_github_evidence.py` with provider ID, app producer, raw outcome and hashed payload; verify optional green can report auxiliary health and optional red remains visible without invalidating required CI.
- [x] 2.7 Version the new check binding as schema 5 while reading the protected base's published schema 4 during migration; verify a version 4 base emits valid version 4 required-CI evidence, version 4 rejects the new binding, and mixed inventory/evidence versions fail.

## 3. Documentation and bounded verification

- [x] 3.1 Document each provider field, Git-object source, bundle hash and claim boundary in `docs/ci/gate-evidence-contract.md`; verify the documentation matches the emitted fixture bundle and contains no merge or post-merge authorization claim.
- [x] 3.2 Run focused collector and existing contract tests plus `scripts/precheck.sh`, record the exact passing gates, and fix any failure in the scoped files; verify the commands exit successfully and `git diff --check` is clean. No Lean target is changed, so no local Lean build is needed.
- [ ] 3.3 Exercise the controller evidence command read-only against one open PR and record its exact base, head, candidate, run/attempt and output classification in the PR description; verify no GitHub mutation occurred and that incomplete provider evidence yields a denied claim rather than a substituted value.
- [ ] 3.4 Freeze the exact implementation commit for independent mathematical/source-faithfulness, repository-boundary, abstraction/adoption and mathlib-style review (at most three review/improve rounds); verify all four reviews address the same final commit and unresolved findings are recorded rather than bypassed.
- [ ] 3.5 Open the ordinary PR for owner review with only the planned files, obtain its required hosted pull-request CI result and record any self-hosted manual dispatch separately if used; verify the final head has a successful required `ci` check and keep durable controller admission and workflow edits out of this PR.
- [ ] 3.6 After human `trust-reviewed` and independent workflow/controller owner signoffs, merge the PR normally, verify the published merge revision and live controller evidence, record exact review/CI/merge links on #1430, and close it only when its acceptance evidence is complete.
