# Tasks

## Bootstrap record (completed before code-ledger initialization)

The initial plan-only bootstrap created issue #1469 and its mutation-disabled
manifest, passed strict validation and adversarial review, and merged as PR
#1470. GitHub interpreted negated closing language as a close reference; the
issue was reopened and the merged PR body corrected. The closure-contract and
self-bootstrap update (the former task 1.5) merged as PR #1474. Its title,
body, source commit message (`docs(loop): harden revalidation publication
plan`), and squash commit message (`docs(loop): tighten revalidation safety
plan`, with a non-closing body) contained no closing instruction; provider
`closingIssuesReferences` was empty, and issue #1469 is open. That update
specifies the nine closing verbs, repository-qualified identities, creation
readback, explicit squash messages, and the one-time owner-authorized
self-bootstrap. The current planning update adds an explicit task-progress
digest mode with legacy raw-digest compatibility and must merge before the
code ledger is initialized. These completed bootstrap milestones are recorded
as evidence here rather than checked task lines, so the ledger's initial
digest has every numbered completion marker in its canonical unchecked form.

## 1. Initialize the bounded controller work

- [ ] 1.1 From a fresh clean-base checkout after the planning update merges, run `validate` and read-only `preflight`, create the manifest's exact planned issue branch, and initialize its ledger before source edits; verify the initialized ledger freezes the expected controller files, exact issue, three-round cap, and artifact digests. Keep every mutation flag disabled throughout this code run.

## 2. Implement passed-head revalidation as one frozen code chunk

- [ ] 2.1 Pin protected-base OIDs at new ledger initialization and per ordinary/revalidation round; add append-only revalidation history validation and an atomic passed-head transition that reserves exactly one next capped round. Verify a disposable legacy-schema fixture mirroring #928's r1 needs-changes / r2 pass / cap-3 history uses only the marked conservative base inference, without altering the active DT1 ledger, and a repeated ordered refresh chain consumes successive slots without permitting a skipped or fourth round.
- [ ] 2.2 Add fail-closed admission checks for exact local HEAD, direct protected-base ancestry, clean/frozen diff, manifest and OpenSpec binding, open issue, remote identity, and a complete all-state exact-branch PR lookup that accepts only no PR or one open, non-draft PR exactly bound to the prior pass; verify both closure-mode bodies and the live provider `closingIssuesReferences` match before admission, and each malformed, failed, stale, truncated, or ambiguous check leaves ledger bytes unchanged.
- [ ] 2.3 Bind all shipping actions to the latest complete passing head and verify local, remote, and provider heads remain exact; prove pending refresh, stale local/remote head, and pre-merge base drift fail before mutation, a refreshed third-round needs-changes outcome becomes terminal blocked, safe exact-head push synchronizes only the absent or immediately prior remote ref, an exact existing open PR is reused rather than duplicated, stale/closed/merged/draft/multiple PRs reject refresh, and closure verifies the exact merged PR/issue/base ancestry.
- [ ] 2.4 Add focused controller documentation, usage examples, a new friction-log entry for the stale-pass/base-refresh failure, and focused tests; verify `python3 -m unittest discover -s scripts/tests -p 'test_loop_engine.py'`, `python3 scripts/precheck.sh`, and strict OpenSpec validation pass.
- [ ] 2.5 Harden PR issue-link validation: scan all nine GitHub closing verbs case-insensitively, with/without optional colon, across title, body, and every source commit message; accept only a standalone canonical `Closes #N` body line for complete chunks and a non-closing reference for progress chunks; compare provider identities by owner/repository plus issue number; verify exact references immediately after PR creation and before refresh admission and every approval/merge/closure path; use explicit safe merge subject/body, including squash; add table-driven syntax, negation/quote, foreign same-number issue, positive/negative, progress, missing/truncated-data, generated-merge-message, creation-readback, and provider-mismatch tests.
- [ ] 2.6 Implement the explicit `raw`/`task_progress` OpenSpec digest modes, with absent mode retaining raw behavior; normalize only checked/unchecked markers on top-level, non-fenced task lines in the registered `tasks.md`, canonicalizing to `[ ]`. Test all-unchecked digest equality with the old raw baseline; `[ ]`/`[x]`/`[X]` toggles; task wording, IDs, order, surrounding text, non-task checkbox, quoted/nested/fenced lookalikes, other artifacts, and raw-mode byte-sensitivity; verify pre-existing legacy ledger and recovery-registry digests remain valid without migration.

## 3. Adversarial review and handoff

- [ ] 3.1 Run independent mathematical/source-faithfulness, repository-boundary, abstraction/adoption, and controller-style reviews against one exact commit, revise only within the frozen files and three-round cap, and verify the ledger records all required roles against the final SHA.
- [ ] 3.2 After all four reviews pass on one exact SHA, publish this controller's PR through the one-time owner-authorized procedure specified in design.md, not the stale protected-base mutation actions; wait for required hosted CI after PR creation, then re-read CI, exact local/remote/PR head, frozen paths, issue, title/body/commit messages, provider closure references, and protected-base freshness before merging with the frozen `squash` method, head match, and explicit safe subject/body. Verify the resulting merge/issue state. If CI fails, the cap is exhausted, or protected base moves without capacity, preserve evidence and stop without resetting the attempt.
