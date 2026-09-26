# Design

## Context

See [proposal.md](proposal.md#why) and [the spec delta](specs/loop-engineering/spec.md). The controller already has two distinct facts: an ordinary review panel may pass, and merge is separately gated by live required checks. The merged protected-base revalidation path also permits a bounded number of changed-head panels, but it does not bind a code revision to failed CI evidence and those panels do not consume the configured critique/revise cap.

The controller and its tests are owned by `scripts/loop_engine.py` and `scripts/tests/test_loop_engine.py`. This is a control-plane change only: no Lean declaration, mathematical owner, import edge, audit slice, or public abstraction changes. The new tracking issue is #1483; the new workflow state must not be folded into the in-flight SF8 issue #554 or the separate protected-base revalidation contract.

## Goals / Non-Goals

**Goals:**

- Preserve passed-panel evidence while admitting a code-repair panel only from a live required-check failure tied to the exact current PR head.
- Charge every CI-driven repair panel to the existing frozen `max_review_rounds_per_chunk` budget, with the same four independent reviewers and exact-commit binding.
- Reuse live repository, issue, PR, remote, and frozen-scope checks; fail closed before changing ledger state when any evidence is missing or inconsistent.
- Keep pending repairs non-publishable and keep merge gated on green required checks for the exact current PR head.
- Add regression tests and record the stale-worktree / uncharged-revalidation discovery in the observation and friction logs.

**Non-Goals:**

- Changing the legitimate same-reviewed-change revalidation behavior, historical manifests, or existing ledgers. The currently overbroad generic revalidation command must be narrowed so its label matches its intended base-only contract.
- Resuming recovery-managed or already blocked ledgers, increasing any cap, or authorizing a replacement ledger for a frozen chunk.
- Modifying PR #1471, the SF8/SF9 Lean code, or the mathematical scope of issue #554.
- Treating a failed, pending, cancelled, or absent check as approval to publish.

## Decisions

### Use a distinct, charged CI-repair transition

Keep the existing `revalidation` round kind only for a candidate that carries the same reviewed change across a protected-base movement that affects the reviewed scope. On the reviewed base, the generic `ensure_review_round` path currently accepts any different commit and does not itself verify that base movement caused it; implementation must tighten this classifier rather than trusting the current label. A changed implementation made in response to failed CI is different: it is a critique/revise cycle, so the controller records a `ci_failure_repair` event and creates the next ordinary review round. That round is counted by the manifest's original cap; it must not pass through the uncharged revalidation allowance.

When a passed ledger receives a changed candidate, compare its reviewed content against the provider-reported current base. A revalidation may use the uncharged path only when the reviewed-change fingerprint is unchanged and protected-base movement affects the reviewed scope. A changed implementation fingerprint must use the CI-repair path and show a qualifying failure on the current open PR head; otherwise it is refused. Test both classifications so a caller cannot relabel a code revision as a free revalidation.

Alternative rejected: reset the old ledger or import its pass into a new one. Both would detach evidence from the original scope and could replenish the cap. Rewriting the original adjudication is also prohibited; the repair authorization is an appended event.

### Bind admission to one coherent provider snapshot

Read the planned PR's full head SHA, state, draft flag, source branch, source repository, base branch, and issue-link metadata from the configured repository. Require the PR head repository to equal the configured manifest repository. Read check runs and legacy status contexts for that exact commit SHA, including the check-run `head_sha`/status SHA and app identity where available, then compare returned head identities with the PR and live remote source ref. At least one check must be both declared required by the frozen manifest and currently required by branch protection, with a completed `failure` conclusion; match the full identity (check name/context and app identity when provided), not name alone. For this admission transition, failure to read protection, an empty/malformed or contradictory protection response, a stale check, a pending or cancelled conclusion, an optional-check failure, an ambiguous PR lookup, or a moved head stops admission without writing. After fetching statuses, reread the PR and remote source ref and reject if either SHA moved; the local controller lock cannot make provider reads atomic. The green-check gate also requires a live protection read since #1501; neither path has a manifest fallback when that read fails.

Post-merge correction (#1559): the check-run API defaults to a completion-time `latest` filter. CI-repair admission must request `filter=all`, require a complete response, and compare duplicate attempts by their start or creation clock. A newer pending rerun blocks an older completed failure, even when that failure completed later. Missing or mixed clocks remain ambiguous and reject admission. PR #1509 merged before its final-head CI failed, and its exact-final-head four-role review is not evidenced; the unchecked closeout tasks below must not be treated as completed by this correction.

Record each event append-only in `state.ci_failure_repairs`, the existing ordinary ledger. Fields include sequential event number, disposition, PR number and branch, prior passing round, failed-head SHA, exact required check identity/conclusion/run identifier and URL, proposed repair SHA, provider base/head snapshot, and admission timestamp. Keep `state.rounds` as the only review-history and cap-counting root. With a slot remaining, atomically append the event and a `kind: ci_failure_repair` ordinary round at the next adjacent number, then set normal status to `reviewing`. With no slot, append the event with `disposition: cap_exhausted`, set `status: repair_exhausted`, preserve the prior passing round untouched, and allocate no round. Reuse the existing repository-wide controller lock and atomic ledger writer so the provider snapshot and transition are serialized locally. The provider operation is read-only; it does not push, create, ready, approve, merge, or close anything.

The existing PR status-rollup helper can be factored into a structured snapshot shared by green-check validation and failure admission. The snapshot must retain the full PR head and must not select an older same-name check from a different commit as evidence for the current head.

### Preserve ordinary round numbering and terminal behavior

The admission event references the last completed passing round but never edits it. A repair round uses the next adjacent round number and a full 40-character candidate SHA descended from the failed PR head. It is an ordinary charged panel; every reviewer must submit captured output for that same SHA. If a repair round needs changes, the subsequent ordinary critique/revise round remains part of the same cap; publication stays denied until a later ordinary round passes. A repair event is resolved only when the current ordinary ledger has a passing round at or after its linked repair round. Repeated CI repair is permitted only after the latest panel passes and another exact-head required-check failure is observed, and only while an ordinary round remains. When the cap is exhausted, keep the failure evidence and mark the objective `repair_exhausted`/terminal; do not invoke blocked-history recovery, reset counters, rename the chunk, or create a successor ledger for the same work.

If CI is rerun successfully on the same already-reviewed head before a repair transition is recorded, no code revision or review slot is needed: the existing merge gate can use the latest green result on that exact SHA. Once a repair round is admitted, no shipping action is allowed until that round passes.

### Keep publication and mathematical boundaries unchanged

Use the same ordinary ledger as the sole action authority. Add required `--ledger` to `push` and `close`; `push` resolves its issue by the current `agent/<slug>` branch and requires exactly one matching selected manifest entry, while `close` requires the ledger issue to equal `--issue`. A shared ledger-binding helper checks spec id/digest, frozen issue/chunk, and OpenSpec digest where applicable. Every path that can publish, ready, attest, approve, merge, or close calls one common repair-state guard before provider mutation. It denies a cap-exhausted event and denies an allocated event until a passing ordinary round at or after that event's repair round is latest; it also rejects stale or mismatched ledger bindings. Preserve initial draft-PR creation behavior when no CI-repair event exists. After the repair panel passes, existing exact-head and merge-policy checks still apply, with a fresh required-check read immediately before merge. The controller issue's bootstrap manifest remains mutation-disabled; this work grants no implicit provider authority.

Enforce no replacement ledger without introducing a second registry: for this protocol, keep ordinary ledger paths within the repository's existing `.loop-runs` root, scan that root recursively at initialization, and identify a frozen chunk by issue number, issue slug, and chunk id rather than a caller-selected filename or spec id alone. Reject `--state-dir` paths outside `.loop-runs`. Add tests for an existing ledger in a sibling nested state directory and for an unsupported external-in-repo path; the original ledger bytes and `repair_exhausted` status must remain intact.

The reviewers remain independent and cover four lenses on each exact candidate: mathematical/source faithfulness (confirm no mathematical claim is upgraded), repository boundary, abstraction/adoption, and controller/style compatibility. Because there is no Lean API change, a Lean build is not a verification claim; focused Python tests, OpenSpec validation, `scripts/precheck.sh`, and hosted CI are the relevant gates. Each frozen implementation chunk is limited to three critique/revise rounds.

### Frozen implementation chunk

The single implementation chunk, `loop-passed-ci-failure-recovery`, will freeze these paths in its manifest:

- `scripts/loop_engine.py`
- `scripts/tests/test_loop_engine.py`
- `docs/architecture/loop-recovery.md`
- `docs/architecture/loop-engineering-friction.md`
- `.claude/loop-specs/README.md`
- `.claude/skills/run-loop/SKILL.md`
- `.claude/loop-specs/loop-passed-ci-failure-recovery.yaml`

The proposal, spec, design, and task artifacts are frozen by the controller's OpenSpec digest. No Lean source path or other controller manifest is authorized by this chunk.

## Risks / Trade-offs

- **Provider check data is stale or ambiguous** → Bind every status to the full PR head SHA, reread immediately before admission/publication, and fail closed on malformed or incomplete data.
- **A transient CI failure would cause unnecessary review churn** → Do not admit a repair merely because a failed check exists; a green rerun on the same reviewed SHA stays on the existing path and consumes no review slot.
- **A repair bypasses the cap by looking like base revalidation** → Compare the actual reviewed content; route changed code through a charged CI-repair round, keeping base-only revalidation separate.
- **Existing ledgers or manifests have older shapes** → Do not rewrite them. Apply the new transition only to ordinary ledgers whose current manifest and OpenSpec digests validate; keep recovery-managed state on its existing protocol.
- **The controller is being changed by the controller's own workflow** → Keep the bootstrap manifest mutation-disabled and use the separately reviewed, exact-commit controller publication procedure; no self-authorized provider action is implied.

## Migration Plan

1. Keep issue #1483 and this OpenSpec contract separate from #1471. Add a one-issue, one-chunk, three-round manifest with all eight provider mutation capabilities explicitly disabled. Publish only the plan/manifest in the one-time owner-authorized planning bootstrap specified here (an explicit adaptation using the exact-state safeguards in `passed-ledger-head-revalidation`, not a previously documented generic planning-PR procedure): title and commit messages contain no issue-closing keywords; body uses only `Refs #1483`; before merge verify the PR has no `closingIssuesReferences`, the issue is open, and its exact diff contains only the plan/manifest; require current hosted checks green on the exact PR head and reread PR head/base plus issue state immediately before the authorized merge; merge with `gh pr merge --squash --match-head-commit <reviewed-head>` so a moved head is rejected; after merge verify #1483 remains open. Do not describe this as the normal loop workflow: current guidance says the plan normally travels in the work PR.
2. Start implementation only from a fresh clean worktree at the exact reviewed base. Run focused tests for exact-head evidence, immutable history, charged slot accounting, cap exhaustion, and shipping refusal; do not mutate the #1471 ledger to test the new code.
3. Obtain the full four-role panel on the same implementation commit, run `scripts/precheck.sh --no-build` and strict OpenSpec validation, and use hosted PR CI for the controller change. Because this is the controller that will enforce its own publication gates and its bootstrap manifest has every provider mutation disabled, adapt the exact-state safeguards from the one-time owner-authorized controller bootstrap in `openspec/changes/passed-ledger-head-revalidation/design.md` (Migration Plan step 3): verify the exact reviewed SHA, frozen path set, issue/PR state, protected base, and clean local/remote state before publishing; create one PR whose title and commits have no closure directives and whose body has exactly the manifest-required closure reference (`Closes #1483` for this chunk's `complete` closure); wait for hosted CI; re-read required checks and exact PR/source/base state immediately before merge; merge with `gh pr merge --squash --match-head-commit <reviewed-head>` and stop if the server rejects that match; verify the merged state and #1483 closure afterward. Immediately before merge, check the exact protected base's active trust-review policy. If it requires `trust-reviewed`, stop for the repository owner to read the guarded diff and add the label; the agent must not apply it. The current protected base removed that gate in #1449, so do not infer that it remains active from stale checkout guidance. Do not use stale controller mutations or treat this exception as standing authority for later loop runs. Report these checks separately from any local result.
4. This controller issue ends after its own PR closes #1483; it does not modify any consuming implementation PR. A later consumer must start from its own frozen scope and current open non-draft PR, refresh source/base/required-check state, and admit changed code only from fresh exact-head failure evidence. Failure details in #1483's context are motivation only and must never be reused. Do not close dependent or unrelated issues by side effect; each closure must be authorized by that consumer's manifest.

## Open Questions

None. The exact provider fields and concurrency tests belong to implementation discovery, but they cannot change the acceptance boundary in the spec.
