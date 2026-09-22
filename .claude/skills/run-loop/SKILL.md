---
name: run-loop
description: Take a GitHub issue or milestone to merged PRs without owner input — plan in the work PR, four independent reviewers, change-bound ledger, owner-controlled provider authority, and bounded automatic research recovery.
---

# Unattended issue loop

Hand this skill one GitHub issue, or a milestone. It plans, implements, reviews
and lands each issue without asking the owner anything. The issue body is the
specification: its goal, definition of done, deliverables, dependencies and
closure mode are what the run must deliver. The four independent reviewers are
the check on the run's work; the owner is not in the loop.

## When the run stops

Stop for these reasons only:

1. The run needs something only the owner can supply: a password, a token,
   `sudo`, or a provider action the controller reports as not authorized.
2. Continuing would bypass a required check, rewrite `main`'s history, or merge
   with administrator override.
3. An issue's definition of done is false or self-contradictory as written, and
   a research pass (Phase 2.5, or a dispatched researcher when recovery is not
   configured) has confirmed it.
4. Every selected issue is merged, parked, or out of budget: the run is over.

Everything else is a decision the run makes, records, and moves past. Record
decisions in the PR body. Record tooling or documentation friction in
`docs/architecture/loop-engineering-friction.md`. Record out-of-scope work as a
follow-up issue (`action follow-up`). Then continue. Never end a turn with a
question whose honest answer is "yes, continue", and never ask the owner to
confirm a plan, an edit, a scope reading or the next step. When a stop reason
blocks one issue, leave that issue's state recorded and work the others. Report
every stop together at the end.

These are not stops. What to do instead:

- **Stale issue text** (a closed blocker, a retired path). Use the live state,
  note the discrepancy in the PR body, and file a follow-up if the issue needs
  rewriting.
- **Retired required check.** When a manifest names a check that branch
  protection no longer requires, preflight warns and merge uses the live list.
- **Frozen scope is too narrow before the ledger exists.** Edit the plan; it
  is in the PR. After the ledger exists, use a declared `lift_targets` path, or
  record the gap and file a follow-up.
- **Ambiguous design choice.** Take the smallest reading that meets the
  definition of done, and state it in the PR body.
- **`main` moved.** Rebase, or merge `main` into the branch. A passed review
  carries over when the change is unchanged, and a changed one needs one
  revalidation round (Phase 3).
- **Round cap exhausted.** With `recovery` configured, run Phase 2.5. Without
  it, preserve the ledger, park the chunk, file a follow-up issue that carries
  the unresolved findings, and take the next issue.
- **The OpenSpec CLI is missing.** Structural validation is used instead, and
  preflight warns.
- **A reviewer returns nothing.** Re-dispatch that role on the same commit.

## Invariants

- Work in a dedicated `agent/<slug>` worktree whose history contains the
  manifest's `base_ref`. Fetch the remote first, and seed the worktree's build
  cache (`bash scripts/seed_worktree_cache.sh`).
- Execute only the issues and frozen chunks the manifest lists. Never select a
  replacement issue because a listed issue is hard; a hard issue is Phase 2.5's
  job.
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
  exhausted attempt. Without recovery, park the chunk and file its follow-up
  (Phase 2); with recovery, execute Phase 2.5 automatically within the
  cumulative budget.
- A successor using `predecessor_prs` may start only after every named source
  PR has the exact controller attestation, reviewed head, and merge commit
  pinned in the manifest; its merge must be an ancestor of both `base_ref` and
  the current HEAD. The controller repeats that check at ledger initialization
  and every successor PR action. A source manifest with
  `predecessor_attestation.emit: true` must run `action attest-pr` after its
  passing ledger and before its controller merge.
- Do not silently re-chunk, widen the file list, or rewrite the plan after
  review evidence exists. Recovery preserves that contract. Renaming a chunk,
  manifest, state directory or worktree cannot reset an objective's history or
  allowance; newly required scope is not automatic authority.
- Never run `scripts/gates.sh` locally. Use `scripts/precheck.sh` with a
  targeted build where the repository hook permits it; the self-hosted runner
  is the CI verdict.
- Use only `scripts/loop_engine.py action ...` for comments, pushes, PR
  creation, marking ready, follow-up issues, approval, merge, and issue
  closure. Do not call `gh issue close`, `gh pr ready`, `gh pr merge`,
  `gh issue create`, `gh pr review`, or `git push` directly from this skill.
- Provider authority comes from `origin/main` only: a manifest merged there
  keeps its reviewed grants, and `.claude/loop-authority.yaml` holds the
  owner's standing grants for manifests written on a work branch. Never write
  or edit that file from a run, and never widen a grant in a manifest.
- Code issues close only after the controller verifies a merged PR that closes
  the same issue. Non-PR closure is disabled unless the manifest explicitly
  says otherwise.

## Phase 0: plan inside the work PR

For a milestone, list its open issues (`gh issue list --milestone <title>`),
order them by their dependencies, and run Phases 0–3 once per issue. An issue
whose live blockers are open outside the milestone is skipped with a recorded
reason, not waited on.

1. `git fetch origin`, then create the `agent/<slug>` worktree from
   `origin/main`, where `<slug>` is a short kebab-case name for the issue.
   Read the issue with `gh issue view <n> --comments`. Its body is the
   specification.

2. Write the manifest at `.claude/loop-specs/<slug>.yaml` on that branch. The
   minimal single-issue shape is in `.claude/loop-specs/README.md`. Derive each
   chunk's `acceptance` from the issue's definition of done. Derive its `files`
   from the issue's deliverables plus the audit, umbrella and backlog files the
   repository rules require; a new public declaration needs its audit record
   and its umbrella export. Set `closure: progress` only when the issue's
   definition of done is explicitly multi-PR. Add an OpenSpec change only for
   a multi-issue batch, or when the issue asks for a design. Write its
   artifacts directly: do not invoke `$openspec-propose` inside a run, because
   that workflow ends by waiting for a new request.

3. Validate and preflight:

   ```text
   python3 scripts/loop_engine.py validate --spec <manifest>
   python3 scripts/loop_engine.py preflight --spec <manifest>
   ```

   The plan may be uncommitted or committed on the branch. Preflight fails
   only on:
   - uncommitted work outside the plan;
   - a branch that does not contain `base_ref` (rebase and rerun);
   - a wrong actor or remote;
   - an issue that is closed, labelled `blocked`/`research`/`type:spike`, or
     has live blockers;
   - another branch's open PR for the same issue;
   - a stale predecessor attestation;
   - a failing roadmap gate.

   Repair what is repairable and rerun. An ineligible issue is recorded and
   skipped.

4. Commit the plan as the branch's first commit.

5. Read `docs/architecture/generalization-backlog.md` before choosing an
   implementation approach. A recorded lift may already say where this work
   belongs, or record that the obvious generalization is false.

6. Do not claim an issue by hand. When comments are authorized, the
   controller's comment action may post a one-line link to the branch.

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
- If recovery work may need new lift dispositions, include
  `docs/architecture/generalization-backlog.md` in the original frozen file
  list before initialization. A lift finding does not implicitly authorize
  editing that file or widening the manifest.

Running neither advisor is permitted when the manifest names none. Running one
and not the other is not: they are blind in different directions, and the one
you skip is the one that finds the hypothesis nobody thought to question.

## Phase 1: one frozen chunk

For each issue in manifest order:

1. Re-run the live preflight and initialize the exact ledger entry:

   ```text
   python3 scripts/loop_engine.py ledger init --spec <manifest> \
     --issue <number> --chunk-id <chunk-id>
   ```

   For a selected dependency, initialization refuses to proceed unless every
   predecessor chunk has a passing, digest-matching ledger. For a
   `predecessor_prs` entry it additionally rechecks the live provider
   attestation and both ancestry bindings.

2. On the issue's `agent/<slug>` branch, implement the frozen chunk: its
   acceptance statements, and the unchecked OpenSpec tasks when a change
   exists. Tick task boxes and append the observation log as you go; the v2
   plan digest ignores both. Keep the issue's mathematical hypotheses
   explicit; an interface field is not a proof.

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
python3 scripts/loop_engine.py ledger record-review --state <ledger> \
  --reviewer <name> --commit <sha> --verdict pass|pass_with_lift|needs_changes|blocked \
  --finding-file <path to that reviewer's verbatim final message>
```

Write each reviewer's final message to its own file and pass the path. The
controller stores the text and its digest, and refuses to adjudicate a round in
which any reviewer row lacks captured output. `--finding` remains available for
a one-line summary only; it is not evidence and cannot stand alone.

Only after every required reviewer has submitted, adjudicate:

```text
python3 scripts/loop_engine.py ledger adjudicate --state <ledger> \
  --verdict pass|pass_with_lift|needs_changes|blocked --note "<decision>"
```

If the result is `needs_changes` and fewer than the manifest's configured cap
have been used, fix only the recorded findings, rerun the targeted checks,
commit, and repeat Phase 2. If the result is `blocked` or the final permitted
round still needs changes, preserve that result and run Phase 2.5 when recovery
is configured. Otherwise park the chunk:
- keep the ledger unchanged;
- file a follow-up issue carrying the unresolved findings verbatim
  (`action follow-up`);
- record the chunk in the end-of-run report;
- continue with the next issue.

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
  record its disposition in `docs/architecture/generalization-backlog.md` as an
  `UNVERIFIED` row within the already-authorized scope. Recovery passing
  adjudication and publication require a complete visible row in the exact
  reviewed commit's ordinary file blob; HEAD and dirty worktree text cannot
  supply it. Follow the exact row format in `docs/architecture/loop-recovery.md`.
  If the row is first discovered after freezing, preserve the current reviews,
  adjudicate `needs_changes` (or abandon an incomplete panel), append the row,
  commit, and allocate a new full panel. The new SHA costs another round; never
  rewrite a review or claim an unreviewed backlog append costs no round. Apply
  automatic recovery if the attempt is exhausted. An existing valid committed
  row can satisfy the gate without another source change.
- When dispatching the style reviewer for a controller ledger, require its
  controller verdict: `PASS` for an acceptable chunk, `NEEDS_CHANGES` for
  required repairs, or `BLOCKED` for an unreconstructable claim. `MERGE` is
  only its standalone review vocabulary; the controller does not map it.
  In recovery mode require the exact `Reviewed commit:` / `Close:` trailer,
  with `PASS`, `PASS_WITH_LIFT`, `NEEDS_CHANGES`, or `BLOCKED` as appropriate.
  Preserve the reviewer's message verbatim; never append a verdict mapping.

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

## Phase 3: handoff through merge

The PR can open as soon as the plan commit exists: CI then runs while the
panel reviews. It must not be marked ready or merged before the ledger passes.

1. Push and create the PR through the controller (`action push`,
   `action create-pr --draft`), supplying the ledger. The PR body states the
   decisions the run made and links the issue. Use a closing keyword for a
   complete chunk and `Refs #<n>` for a progress chunk.
2. When the ledger passes, run `action ready`. It rechecks the passing ledger,
   the plan digest, the frozen files, and that the PR head carries the reviewed
   change.
3. Wait for the required checks (`gh pr checks <n> --watch`). Branch protection
   decides which checks are required; a manifest check it no longer requires is
   ignored. Local precheck is evidence for debugging, not a CI verdict. A red
   check is a finding: fix it, commit, and take the new commit through Phase 2
   as the next round.
4. If `main` moved, merge `origin/main` into the branch (or rebase), rerun the
   targeted checks, and push. A head that carries the same change keeps the
   pass. If the change moved, as a conflict resolution does, run one
   revalidation panel on the new commit. It needs all four reviewers and does
   not spend the improvement cap; at most two are allowed.
5. If `predecessor_attestation.emit` is true, run `action attest-pr` after the
   ledger passes and before merging. It binds the current PR head.
6. Run `action merge`. The controller pins `--match-head-commit` to the head it
   just verified, so a later push makes the provider refuse the merge instead
   of landing unreviewed content. Administrator merge is never inferred from a
   failed check.
7. The closing keyword closes a complete chunk's issue on merge. Use
   `action close --merged-pr` only when it did not. Then take the next issue.

When the controller reports that an action is not authorized, that is stop
reason 1 for this issue only. Leave the PR in its current verified state,
record it, and continue with the other issues. In stack mode, a dependent
issue waits on its predecessor's merge; work the independent issues meanwhile.

At the end, report:
- the issues merged, with their PRs;
- chunks parked, each with its follow-up issue;
- provider actions actually taken;
- CI status;
- lift findings carried to the generalization backlog, each with its leaf
  declaration and proposed ancestor;
- every stop reason hit, and the exact grant or input it needs.
