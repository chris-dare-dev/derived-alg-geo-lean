---
name: run-loop
description: Execute enabled OpenSpec-backed work with a digest-bound ledger, four independent reviewers, guarded provider actions, and optional bounded automatic research recovery.
---

# Bounded OpenSpec loop

This skill is the outer protocol for an explicitly enabled manifest under
`.claude/loop-specs/`. It may run unattended only after the manifest itself has
been reviewed and `enabled: true` is present. The manifest is the user's
forward approval for the listed goals and separately named provider actions; do
not infer permission from ordinary issue text or from a green build.

OpenSpec is the requirements source. Use the generated Codex skills
`$openspec-explore`, `$openspec-propose`, `$openspec-apply-change`,
`$openspec-update-change`, `$openspec-verify-change`, and
`$openspec-archive-change` according to the artifacts present. Do not edit
generated `.agents/skills/` files.

## Invariants

- Work in a clean dedicated worktree based on the manifest's exact `base_ref`.
- Execute only the one to three issues and frozen chunks listed in the
  manifest. Never select a replacement issue because a listed issue is hard.
- Run the mathematical, repository-boundary, abstraction, and mathlib reviewers
  independently on the same commit. The style reviewer cannot substitute for
  either adversarial lens.
- A reviewer's own final message is the evidence. If a dispatched reviewer
  returns no readable final message, re-dispatch that missing role on the same
  commit. In recovery mode the reserved round stays charged even if abandoned.
  Never substitute your own inspection of the diff
  for a reviewer verdict, and never paraphrase a reviewer's output into the
  ledger in place of its text. Record the verbatim message with
  `--finding-file`; the controller refuses to adjudicate a round whose reviewer
  rows carry no captured output.
- Altitude and generalization findings are expected output, not churn. A
  reviewer that reports none on a chunk has probably not looked.
- A review/improve round is keyed by the commit and frozen chunk. A changed
  commit starts the next round. New work permits at most three rounds per
  attempt; explicit legacy manifests retain their recorded caps. Preserve an
  exhausted attempt. Without recovery, stop the chunk; with recovery, execute
  Phase 2.5 automatically within the cumulative budget.
- A successor using `predecessor_prs` may start only after every named source
  PR has the exact controller attestation, reviewed head, and merge commit
  pinned in the manifest; its merge must be an ancestor of both `base_ref` and
  the current HEAD. The controller repeats that check at ledger initialization
  and every successor PR action. A source manifest with
  `predecessor_attestation.emit: true` must run `action attest-pr` after its
  passing ledger and before its controller merge.
- Do not silently re-chunk, widen the file list, or rewrite the OpenSpec plan
  after review evidence exists. Recovery preserves that contract. Renaming a
  chunk, manifest, state directory or worktree cannot reset an objective's
  history or allowance; newly required scope is not automatic authority.
- Never run `scripts/gates.sh` locally. Use `scripts/precheck.sh` with a
  targeted build where the repository hook permits it; the self-hosted runner
  is the CI verdict.
- Use only `scripts/loop_engine.py action ...` for comments, pushes, PR
  creation, approval, merge, and issue closure. Do not call `gh issue close`,
  `gh pr review`, or `git push` directly from this skill.
- Code issues close only after the controller verifies a merged PR that closes
  the same issue. Non-PR closure is disabled unless the manifest explicitly
  says otherwise.

## Phase 0: validate and preflight

1. Identify exactly one manifest and read its referenced OpenSpec proposal,
   delta specs, design, and tasks. Run:

   ```text
   openspec validate --all --strict --no-interactive
   python scripts/loop_engine.py validate --spec <manifest>
   python scripts/loop_engine.py preflight --spec <manifest>
   ```

2. Stop if the manifest is disabled, the OpenSpec CLI is unavailable when its
   validation mode is `cli-required`, the base is not exact, the worktree is
   dirty, the authenticated actor differs, branch protection is missing a
   required check, an issue is closed/blocked/ineligible, a dependency is open,
   a predecessor attestation is missing or stale, a branch/PR already exists,
   or a repository gate fails.

3. Read `docs/architecture/generalization-backlog.md` before choosing an
   implementation approach. A recorded lift may already say where this work
   belongs, or record that the obvious generalization is false.

4. Do not claim an issue by hand. If the manifest authorizes comments, use the
   controller's comment action with a concise link to the OpenSpec change and
   frozen chunk. If it does not, leave the tracker untouched.

## Phase 0.5: pre-freeze altitude sweep

Run once, after preflight passes and **before the first `ledger init`**. The
ordering is the point: once any ledger exists, `digest(spec)` is load-bearing
for dependency checks, so a finding from here can no longer influence a frozen
file list. Before that point it can.

Dispatch both advisors over every planned chunk's scope:

1. `.claude/agents/altitude-scout.md` — is this concept already known, in
   greater generality, in the pinned Mathlib or the literature?
2. `.claude/agents/hypothesis-elimination-scout.md` — which hypotheses does the
   proof not actually use?

They are named in `spec.review.advisors`, not `spec.review.reviewers`. They
record no verdict and nothing waits on them: do not call `ledger record-review`
for an advisor, and do not treat a slow or failed advisor as a reason to stop.
Their entire output is rows in `docs/architecture/generalization-backlog.md`.

Then read the backlog and decide, before freezing:

- A candidate that is `PIN-CONFIRMED` may mean this chunk should consume an
  existing general result instead of proving a special case. Adjust the plan now.
- A verified weakening may mean the chunk's own statements should be written at
  the weaker hypotheses from the start, rather than lifted later.
- A plausible ancestor that this chunk will not touch belongs in the chunk's
  `lift_targets`, so a reviewer can open it later without a manifest edit.

Running neither advisor is permitted when the manifest names none. Running one
and not the other is not: they are blind in different directions, and the one
you skip is the one that finds the hypothesis nobody thought to question.

## Phase 1: one frozen chunk

For each issue in manifest order:

1. Re-run the live preflight and initialize the exact ledger entry:

   ```text
   python scripts/loop_engine.py ledger init --spec <manifest> \
     --issue <number> --chunk-id <chunk-id>
   ```

   For a selected dependency, initialization refuses to proceed unless every
   predecessor chunk has a passing, digest-matching ledger. For a
   `predecessor_prs` entry it additionally rechecks the live provider
   attestation and both ancestry bindings.

2. Create or enter the issue's dedicated `agent/<slug>` branch. Implement only
   the unchecked OpenSpec tasks for the frozen chunk. Keep the issue's
   mathematical hypotheses explicit; an interface field is not a proof.

3. Run targeted Lean checks and `scripts/precheck.sh` as appropriate. Commit
   the chunk. Before creating a PR, the controller checks that the committed
   diff stays inside the frozen path prefixes and that the PR body closes only
   the selected issue.

## Phase 2: adversarial panel and bounded improvement

On the same commit, dispatch all four reviewers independently:

1. `.claude/agents/mathematics-adversary.md`
2. `.claude/agents/repository-boundary-adversary.md`
3. `.claude/agents/abstraction-adversary.md`
4. `.claude/agents/mathlib-reviewer.md`

For recovery-enabled work, reserve the round **before** dispatch:

```text
python3 scripts/loop_engine.py recovery start-round --ledger <ledger> --commit <full-sha>
```

Supply every reviewer the complete inherited finding corpus. Each passing
review must address every inherited finding ID with nonempty evidence in a JSON
object passed as `--resolutions-file <path>` to `ledger record-review`. The
reviewer's verbatim output ends with `Reviewed commit: <full-sha>` immediately
followed by the final line `Close: <TOKEN>`; counts and prose precede those lines.

Record each verdict and finding without paraphrasing away a blocker:

```text
python scripts/loop_engine.py ledger record-review --state <ledger> \
  --reviewer <name> --commit <sha> --verdict pass|pass_with_lift|needs_changes|blocked \
  --finding-file <path to that reviewer's verbatim final message>
```

Write each reviewer's final message to its own file and pass the path. The
controller stores the text and its digest, and refuses to adjudicate a round in
which any reviewer row lacks captured output. `--finding` remains available for
a one-line summary only; it is not evidence and cannot stand alone.

Only after every required reviewer has submitted, adjudicate:

```text
python scripts/loop_engine.py ledger adjudicate --state <ledger> \
  --verdict pass|pass_with_lift|needs_changes|blocked --note "<decision>"
```

If the result is `needs_changes` and fewer than the manifest's configured cap
have been used, fix only the recorded findings, rerun the targeted checks,
commit, and repeat Phase 2. If the result is `blocked` or the final permitted
round still needs changes, preserve that result and run Phase 2.5 when recovery
is configured; otherwise stop the chunk and report the exact ledger state.
Do not ask the same reviewers to rediscover the same issue on an unchanged
commit.

Generalization findings are handled by where the fix lands, not by rationing
them:

- A lift whose target is **inside** the frozen file list is a normal
  `needs_changes`. It is actionable here, so it costs a round.
- A lift whose target is a declared `lift_targets` prefix becomes writable the
  moment the reviewer records it — authorization keys off the recorded review,
  not the adjudication. Adjudicate `needs_changes` to implement it now in the
  now-open ancestor, or `pass_with_lift` to ship the chunk and defer it. Prefer
  implementing it now when it is small; prefer deferring when it cascades.
- A lift whose target is **outside** both the frozen file list and any declared
  `lift_targets` prefix cannot be implemented in this chunk. Do not turn it into a `needs_changes` the chunk cannot satisfy,
  and do not drop it. The reviewer closes `pass_with_lift` with a `--lift-target`;
  append its `LIFT:` block to `docs/architecture/generalization-backlog.md` as an
  `UNVERIFIED` row, then adjudicate the round `pass_with_lift`. The controller
  refuses that adjudication while any named target is still missing from the
  backlog, so the finding cannot be dropped. In recovery mode the allocated
  panel still counts toward the objective budget, even when it passes with a lift.
- The style reviewer closes `MERGE` / `MERGE AFTER FIXES` / `NEEDS REWORK`, not
  the controller's vocabulary. Map `MERGE` to `pass` and both others to
  `needs_changes`. Preserve the reviewer's message verbatim; do not append a
  mapping after its final verdict. The controller performs the token mapping.

Termination is the round cap's job. Never suppress a class of finding to help
the loop converge.

## Phase 2.5: automatic research recovery

Read `docs/architecture/loop-recovery.md`. Recovery is explicit manifest policy.
Poll `python3 scripts/loop_engine.py recovery next --ledger <ledger>` and execute
its next action while this supervising agent is active. The CLI does not launch
agents or keep running after the supervisor exits.

1. Dispatch a researcher with the frozen contract, complete failed
   reviews and remaining budget. Require a reproduced obstacle, diagnosis,
   changed strategy, concrete verification checks and all inherited finding IDs.
2. Submit the structured plan with `recovery submit-plan --ledger <ledger>
   --file <plan.json>`. Dispatch a separate recovery reviewer, distinct from the
   researcher and implementer, against that exact plan and its evidence. Record
   their structured verdict with `recovery review-plan --ledger <ledger>
   --file <review.json>`.
3. On `ready`, execute `recovery resume --ledger <ledger>` and implement the
   accepted strategy. On `needs_changes`, consume the same episode's remaining
   plan allowance. A successor still requires all four implementation reviews.
4. Use `recovery exhaust --ledger <ledger> --reason "<obstacle>"` to abandon a stuck partial attempt;
   its allocation and any returned findings remain charged. Check remaining time
   before dispatch and bound worker duration by it. When the controller parks the
   objective, report the obstacle and continue other already-authorized work.

Do not pause for routine approval of these transitions. Source changes, plan
revisions and research subtasks retain the original scope and budget. Provider
permissions remain separate; a research approval grants none.

## Phase 3: guarded handoff

When the ledger passes:

1. Push and create the PR through the controller, supplying the ledger to bind
   the PR to the frozen file list. Keep it draft until the required review and
   CI policy permits readiness.
2. Wait for the configured required checks as the provider reports them. Local
   precheck is evidence for debugging, not a CI verdict.
3. Approve only through the controller. It rechecks the passing ledger, plan
   digests, PR head, frozen files, and required checks. Provider refusal of
   self-approval is a hard stop, not a reason to bypass branch protection.
4. If `predecessor_attestation.emit` is true, create the source PR's durable
   controller evidence with `python scripts/loop_engine.py action attest-pr`
   after its ledger passes and before merging. It is bound to the current PR
   head; do not hand-write or reuse it for another PR.
5. Merge only if `mutations.merge_pr` is explicitly true and a passing ledger
   is supplied. The merge action also requires the requested method, auto,
   administrator, and branch-deletion behavior to be allowed by the manifest;
   administrator merge is never inferred from a failed check. Otherwise stop
   at the approved PR.
6. Close the issue only after the controller confirms that the merged PR closes
   that same issue. Then re-run preflight before considering the next selected
   issue.

For stack mode, a dependent issue cannot advance while merge authority is
false. Stop with that explicit reason rather than treating an open approved PR
as a closed prerequisite. At the end, report completed chunks, terminal
blocked chunks, provider actions actually taken, CI status, the lift findings
carried to the generalization backlog (each with its leaf declaration and
proposed ancestor), and the next required human decision.
