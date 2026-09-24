# Agent observations

Append-only operational observations for this frozen change. These entries do
not amend the scope or the terminal histories they reference.

## 2026-09-23

- OBS-001: Issues #1458, #1459, and #1460 have no PR and each exhausted its
  review cap. Their final reviews found ledger-evidence, exact-head PR creation,
  and ready-transition gaps. The separately created #1461 and #1462 follow-ups
  also reached their terminal caps. Their branches and ledgers remain untouched.
- OBS-002: The clean worktree starts at current `origin/main`
  `e18e20f9c3768269eedb622da04b9ab9f26ce127`; the primary checkout has unrelated
  dirty/untracked state and is not used for this run.
- OBS-003: `openspec list --specs --json` returned an empty canonical capability
  inventory. This change therefore adds `controller-publication-integrity`
  instead of editing the unarchived `loop-engineering-controller` delta.
- OBS-004: `gh api user` identifies `chris-dare-dev`. The current base has no
  `.claude/loop-authority.yaml`, so the controller has no standing provider
  grants. This manifest is disabled and every mutation is false.
- OBS-005: New tracking issue #1482 is open and names the combined remaining
  controller scope. The primary predecessor is issue #1458,
  `controller-ledger-integrity` / `controller-ledger-integrity-core`, at its
  three-round terminal cap. It is a historical identity, not a continuation.
- OBS-006: One issue and one frozen chunk are selected. The review roster has
  the four established roles plus independent bootstrap-security,
  bootstrap-workflow, and bootstrap-test-design adversaries. No Lean source or
  mathematical API is selected.
- OBS-007: The first lift-record draft tried to put its own reviewed commit SHA
  inside the backlog block. That is self-referential because the block changes
  the commit hash. The accepted binding is the verbatim reviewer marker and
  ledger record digest over the exact Git blob; later lifecycle records name
  the original reviewed SHA.
- OBS-008: `scripts/precheck.sh --no-build` passes every gate except
  `loop-spec`, which rejects the unchanged, already-merged #1394 manifest
  because it still names `agent/issue-1394-plan` as its base. That manifest is
  outside this frozen chunk and remains untouched. Both loop-engine test
  suites, controller manifest validation, and strict OpenSpec validation pass.
- OBS-009: Updating the controller's common review protocol changes a recovery
  test fixture as well as the focused engine tests. Added
  `scripts/tests/test_loop_recovery.py` to this chunk before the first formal
  review; the zero-review seed and its shared bootstrap identity are migrated
  to the corrected manifest and next planning-only commit without resetting
  its status or review history.
- OBS-010: The first seven-role exact-commit panel was recorded and adjudicated
  `needs_changes` on `8bc9ebfc137c783cbeab3abb2e6e6c214acbf23b`. Findings
  require canonical shared bootstrap state before the ignored view, final
  ready-boundary grant revalidation, duplicate provider-path rejection,
  adversarial ledger-history and publication-action tests, exact push-command
  assertions, lift guidance limited to manifest-authorized targets, and an
  explicit owner-only bootstrap publication handoff. The repository-boundary
  and workflow reviewers also found that precheck's loop-spec gate is blocked
  by the already-merged #1394 manifest still using `agent/issue-1394-plan`;
  that path is excluded by the current OpenSpec scope and awaits the user's
  scope decision before it is edited.
- OBS-011: A fresh fetch advanced `origin/main` from the bootstrap's recorded
  base `e18e20f9c3768269eedb622da04b9ab9f26ce127` to
  `4739a0f85ffe62fe014dc669d1a9ee359f7a86b2` through three commits. The #1394
  manifest on that live base is still enabled with
  `base_ref: agent/issue-1394-plan`; it was not changed in this worktree while
  the scope decision is pending. The latest base will be merged into the
  revision before its next exact-commit panel.
- OBS-012: After the round-one fixes and merge of the fetched base, the
  controller suite passes (82 tests), the recovery suite passes (40 tests),
  strict OpenSpec validation passes, this manifest validates, and
  `git diff --check` passes. The permitted `scripts/precheck.sh --no-build`
  still fails only at `loop-spec` because of the same unchanged #1394 manifest
  recorded in OBS-008/011; every other precheck gate passes. No Lean build was
  run. The issue-scope question about the protected manifest remains pending.
- OBS-013: The seven-reviewer round-two panel adjudicated
  `needs_changes` on `2f8bf824e177ed9638b7e1a580a8dd59aed7f983`. Round-three
  repairs add cross-registry rejection of reused terminal predecessor sets and
  identities, explicitly disable recursive submodule pushes, add action-level
  tests for ready snapshot drift, PR-creation preconditions, live authority
  drift, and copied-ledger tampering, and align formal verdict instructions.
  The active ledger's manifest and OpenSpec contract remain byte-for-byte
  frozen; checkbox and observation-log progress remains append-only.
- OBS-014: Round-three focused validation passes: 83 loop-controller tests,
  40 recovery tests, Python compilation, strict OpenSpec validation, manifest
  validation, and `git diff --check`. `scripts/precheck.sh --no-build` still
  fails only at `loop-spec` because the unchanged merged #1394 manifest names
  `agent/issue-1394-plan` rather than `origin/main`; every other reported gate
  passes. The #1394 manifest remains outside this frozen chunk and untouched.
- OBS-015: Merged the latest `origin/main` commit
  `3671d14ce8054f052f3c2672cceb538ecacdeb79` before freezing the next review
  candidate. The integration keeps owner review on legacy provider paths,
  validates ordinary synthetic manifests offline, and makes the adjudicator
  honor the terminal three-round policy consistently. The current focused
  suites pass (89 loop-controller tests and 40 recovery tests), Python
  compilation, manifest validation, and strict OpenSpec validation pass. The
  permitted precheck still fails only `loop-spec` on the unchanged merged
  #1394 manifest; all other reported gates pass. No Lean build or provider
  mutation was run.
- OBS-016: Before recording a round-three verdict, final review caught that
  applying the new three-round limit globally would override explicit caps on
  owner-reviewed legacy manifests. The active cap now preserves those recorded
  legacy limits and applies three rounds to new work; a focused regression test
  covers both cases. After the correction, the loop-controller suite passes
  (90 tests), the recovery suite passes (40 tests), Python compilation passes,
  and `git diff --check` passes. The final-candidate precheck is rerun below
  before the exact-SHA panel.
- OBS-017: On candidate `9bf93ff2778b6bb5ae155983ff254f669b3e9607`, manifest
  validation and strict OpenSpec validation pass. The controller suite passes
  (90 tests), the recovery suite passes (40 tests), and Python compilation
  passes. `scripts/precheck.sh --no-build` reports every gate passing except
  `loop-spec`, which rejects the unchanged merged #1394 manifest because its
  base remains `agent/issue-1394-plan` instead of `origin/main`. That manifest
  is outside this frozen chunk and remains untouched. No Lean build or
  provider mutation was run.
- OBS-018: Research was refreshed against `origin/main` at
  `ce58cc9e44340c07c89836ba2a81fdd07aaee6b4`, which includes #1485's
  CommonMark-aware OpenSpec parsing and #1490's owner-controlled provider
  grants. The recovery manifest still hashes to
  `b9c85b5909a68b5fc120d8be3073e5f391288b08beb4ef2319cd9ed3cfb6ff37`; its
  current OpenSpec digest is
  `9c813e44a65286c703c6218c1e904e2c56b242f28b8a637ba0106e9cf992c51e`.
  The new standing authority grants comment, push, PR creation, and merge by
  default, while this exact recovery manifest explicitly sets every provider
  mutation to `false`, so those grants remain denied for this run.
- OBS-019: On the current main plus owner-prep candidate, the focused loop
  controller and recovery suites pass (141 tests). Strict OpenSpec validation,
  the disabled #1394 manifest validation, the recovery manifest's structural
  validation under the explicit owner-review assumption, and the frozen
  history SHA-256 check pass. The recovery PR #1492 is open as draft; its
  `build` check is pending and `roadmap` passes. The default branch still lacks
  the recovery digest, so enabled validation and live preflight have not been
  attempted. The earlier 12-test-failure/one-error report does not reproduce
  on this base.
- OBS-020: Three inherited findings remain visible in current source: issue
  responses do not validate the returned number or required field shapes;
  malformed/missing `blockedBy` data normalizes to no blockers; and action
  authority is checked before provider reads rather than immediately before
  the mutation. Recovery `action_push` includes `--no-follow-tags` but not
  `--no-recurse-submodules`. These remain in the original frozen scope for
  implementation and action-level regression tests.
