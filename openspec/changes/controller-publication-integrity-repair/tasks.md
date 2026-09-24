# Tasks

## 1. Bootstrap and freeze

The implementation is one frozen chunk, controller-publication-integrity, with
a three-round cap. Its exact file list is:

- AGENTS.md
- CLAUDE.md
- .claude/agents/abstraction-adversary.md
- .claude/agents/altitude-scout.md
- .claude/agents/bootstrap-security.md
- .claude/agents/bootstrap-test-design.md
- .claude/agents/bootstrap-workflow.md
- .claude/agents/hypothesis-elimination-scout.md
- .claude/agents/mathematics-adversary.md
- .claude/agents/mathlib-reviewer.md
- .claude/agents/repository-boundary-adversary.md
- .claude/loop-specs/README.md
- .claude/loop-specs/controller-publication-integrity-repair.yaml
- .claude/skills/run-loop/SKILL.md
- docs/architecture/generalization-backlog.md
- docs/architecture/loop-recovery.md
- scripts/loop_engine.py
- scripts/tests/test_loop_engine.py
- scripts/tests/test_loop_recovery.py
- openspec/changes/controller-publication-integrity-repair

No Lean file or unrelated issue plan is in scope. A terminal third-round failure
blocks this chunk; it does not authorize resetting, renaming, or re-chunking it.

- [x] 1.1 Complete the disabled #1482 manifest and append-only agent-observations.md with the exact reviewed base, distinct #1458/controller-ledger-integrity predecessor, one selected issue, the seven required reviewers, all-zero mutation grants, and a three-round cap; verify manifest tests reject predecessor reuse, wrong base, enabled bootstrap, and cap changes while accepting this identity.
- [x] 1.2 Add the clean-bootstrap first-ledger checks for the clean planning-only descendant, exact reviewed base, dedicated issue branch, and unique objective/ledger identity; verify focused tests reject source or unrelated changes before initialization and any renamed continuation after terminal blockage.

## 2. Frozen evidence and scope

- [x] 2.1 Derive a canonical frozen-selection snapshot from the validated manifest and add one ledger-validation gateway for review, adjudication, dependencies, and publication; verify tests reject mutated copied scope/digests, skipped or excess rounds, missing/extra reviewers, mixed-commit evidence, and forged terminal status while accepting a complete panel.
- [x] 2.2 Enforce exactly one full Reviewed commit marker followed by exactly one terminal Close verdict with no trailing text; verify bare, shortened, mismatched, duplicate, contradictory, and trailing markers are refused and a matching verbatim panel is accepted.
- [x] 2.3 Replace deferred-lift substring matching with uniquely identified append-only finding and lifecycle-transition blocks. Bind the finding block's exact digest and ID to the reviewer, chunk, target, and full reviewed commit through the verbatim review and ledger; lifecycle transitions cite that original commit. Add the finding ID and target to captured evidence and update backlog/reviewer instructions; verify prose, malformed/duplicate IDs, orphan transitions, wrong provenance, and ambiguous commits fail closed.
- [x] 2.4 Use canonical repository-relative paths for lift targets and all changed-file checks; preserve both rename endpoints, validate every provider file entry and changedFiles count, and recognize only a visible proposal Why heading; verify traversal, alias, malformed/truncated payload, out-of-scope rename, fenced/comment/HTML heading tests.

## 3. Publication boundaries

- [x] 3.1 Add the shared immediate live-authority guard before every non-dry-run push/provider mutation; recheck enabled grants, authenticated actor, repository identity, fetch URL, and exactly one effective push destination, and always push an explicit issue-branch refspec with tag following disabled; verify mocked authority drift invokes no subprocess.
- [x] 3.2 Bind source-PR creation to a full terminal passing SHA equal to local HEAD and the live remote issue branch immediately before gh pr create; verify clean worktree, branch, complete scope, command ordering, malformed/missing/moved ref refusal, and post-create head/base/body/file validation.
- [x] 3.3 Harden draft readiness to require a validated passing ledger, exact reviewed PR head, frozen branch/base/body/files, predecessor evidence, and green required checks; compare initial, immediate pre-action, and post-action snapshots and invoke only gh pr ready; verify dry-run, drift, malformed/truncated response, non-green checks, and no-approval/merge/closure tests.

## 4. Guidance and verification

- [x] 4.1 Align AGENTS.md, CLAUDE.md, loop manifest README, run-loop skill, recovery guidance, generalization backlog, and reviewer prompts with actual one-issue runs, exact evidence grammar, durable lift records, disabled bootstrap, action grants, and three-round terminal behavior; verify focused searches find no contradictory issue-count, evidence, or cap instructions.
- [x] 4.2 Run python3 scripts/tests/test_loop_engine.py and python3 scripts/tests/test_loop_recovery.py, python3 scripts/loop_engine.py validate --spec .claude/loop-specs/controller-publication-integrity-repair.yaml, openspec validate controller-publication-integrity-repair --strict --no-interactive, scripts/precheck.sh --no-build, and git diff --check; report each result separately and confirm no Lean build applies.
- [ ] 4.3 Freeze and review one exact candidate SHA with the mathematics/source-faithfulness, repository-boundary, abstraction/adoption, Mathlib/style, bootstrap-security, bootstrap-workflow, and bootstrap-test-design reviewers; preserve every verbatim result in the ledger, repeat the complete panel only for an in-scope revision, and stop terminally on a third unresolved round.
- [ ] 4.4 After and only after a passing panel and fresh exact-head checks, use the documented one-time bootstrap path to publish a reviewable PR; retain the manifest's disabled state and do not self-authorize approval, merge, issue closure, or the trust-reviewed label. Verify hosted PR CI and self-hosted CI separately before the owner-reviewed merge/closure handoff.
