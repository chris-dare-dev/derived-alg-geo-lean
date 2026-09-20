---
name: run-loop
description: Execute one enabled OpenSpec-backed two-to-three-issue formalization batch with a digest-bound ledger, four independent reviewers, guarded provider actions, and a configured five-round cap per frozen chunk.
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
- Execute only the two or three issues and frozen chunks listed in the
  manifest. Never select a replacement issue because a listed issue is hard.
- Run the mathematical, repository-boundary, abstraction, and mathlib reviewers
  independently on the same commit. The style reviewer cannot substitute for
  either adversarial lens.
- A reviewer's own final message is the evidence. If a dispatched reviewer
  returns no readable final message, that round is **void**: re-dispatch it, or
  record `blocked` and stop. Never substitute your own inspection of the diff
  for a reviewer verdict, and never paraphrase a reviewer's output into the
  ledger in place of its text. Record the verbatim message with
  `--finding-file`; the controller refuses to adjudicate a round whose reviewer
  rows carry no captured output.
- Altitude and generalization findings are expected output, not churn. A
  reviewer that reports none on a chunk has probably not looked.
- A review/improve round is keyed by the commit and frozen chunk. A changed
  commit starts the next round; this run permits at most five rounds. After
  the fifth `needs_changes` adjudication, record `blocked` and stop that
  chunk.
- Do not silently re-chunk, widen the file list, or rewrite the OpenSpec plan
  after review evidence exists. A material plan change requires a new manifest
  or a new frozen chunk and fresh review.
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
   a branch/PR already exists, or a repository gate fails.

3. Read `docs/architecture/generalization-backlog.md` before choosing an
   implementation approach. A recorded lift may already say where this work
   belongs, or record that the obvious generalization is false.

4. Do not claim an issue by hand. If the manifest authorizes comments, use the
   controller's comment action with a concise link to the OpenSpec change and
   frozen chunk. If it does not, leave the tracker untouched.

## Phase 1: one frozen chunk

For each issue in manifest order:

1. Re-run the live preflight and initialize the exact ledger entry:

   ```text
   python scripts/loop_engine.py ledger init --spec <manifest> \
     --issue <number> --chunk-id <chunk-id>
   ```

   For a selected dependency, initialization refuses to proceed unless every
   predecessor chunk has a passing, digest-matching ledger.

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

Record each verdict and finding without paraphrasing away a blocker:

```text
python scripts/loop_engine.py ledger record-review --state <ledger> \
  --reviewer <name> --commit <sha> --verdict pass|needs_changes|blocked \
  --finding-file <path to that reviewer's verbatim final message>
```

Write each reviewer's final message to its own file and pass the path. The
controller stores the text and its digest, and refuses to adjudicate a round in
which any reviewer row lacks captured output. `--finding` remains available for
a one-line summary only; it is not evidence and cannot stand alone.

Only after every required reviewer has submitted, adjudicate:

```text
python scripts/loop_engine.py ledger adjudicate --state <ledger> \
  --verdict pass|needs_changes|blocked --note "<decision>"
```

If the result is `needs_changes` and fewer than five rounds have been used,
fix only the recorded findings, rerun the targeted checks, commit, and repeat
Phase 2. If the result is `blocked` or the fifth round still needs changes,
stop the chunk and report the exact ledger state. Do not ask the same reviewers
to rediscover the same issue on an unchanged commit.

Generalization findings are handled by where the fix lands, not by rationing
them:

- A lift whose target is **inside** the frozen file list is a normal
  `needs_changes`. It is actionable here, so it costs a round.
- A lift whose target is **outside** the frozen file list cannot be implemented
  in this chunk. Do not turn it into a `needs_changes` the chunk cannot satisfy,
  and do not drop it. Append the reviewer's `LIFT:` block to
  `docs/architecture/generalization-backlog.md` as an `UNVERIFIED` row and let
  the chunk pass on the merits of the code actually under review.

Termination is the round cap's job. Never suppress a class of finding to help
the loop converge.

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
4. Merge only if `mutations.merge_pr` is explicitly true and a passing ledger
   is supplied. The merge action also requires the requested method, auto,
   administrator, and branch-deletion behavior to be allowed by the manifest;
   administrator merge is never inferred from a failed check. Otherwise stop
   at the approved PR.
5. Close the issue only after the controller confirms that the merged PR closes
   that same issue. Then re-run preflight before considering the next selected
   issue.

For stack mode, a dependent issue cannot advance while merge authority is
false. Stop with that explicit reason rather than treating an open approved PR
as a closed prerequisite. At the end, report completed chunks, terminal
blocked chunks, provider actions actually taken, CI status, the lift findings
carried to the generalization backlog (each with its leaf declaration and
proposed ancestor), and the next required human decision.
