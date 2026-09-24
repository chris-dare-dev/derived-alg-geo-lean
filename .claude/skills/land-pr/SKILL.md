---
name: land-pr
description: Run one unattended landing iteration — select an eligible open PR, update it against main, pre-flight it with scripts/precheck.sh, review it, take the PR CI verdict, then stop. Never merges. Pair with /loop.
---

# One landing iteration

This is **one** iteration against an eligible open PR and it **halts** before
the merge. Merging is a human action, always. Read the issue tracker and native
blockers before selecting a PR; an open PR is not by itself admission-ready.

When called by a bounded loop manifest, the controller's OpenSpec change and
review ledger remain authoritative. Landing may act only on the reviewed head;
the three adversarial lenses plus `mathlib-reviewer` must already have been
recorded for the frozen chunk, and the controller's maximum of three
review/improve rounds still applies, at whatever number the manifest's
`limits.max_review_rounds_per_chunk` sets. This skill's normal one-PR stop behavior
is unchanged.

## What the queue actually is

The historical 28-PR cumulative stack and 90-minute Windows queue have
drained. Current PR branches may be independent, stacked, or in conflict.
Inspect each candidate's base, dependency issues, files and reviewed head.
For a real stack, admit its base first; do not infer stack membership from
file-set inclusion alone. `scripts/pr_queue.py` still uses that older heuristic,
so its ordering is a hint to verify, not authority to admit a candidate.

The required `ci` verdict comes from the `pull_request` workflow on hosted
Ubuntu. Main and manually dispatched runs use the self-hosted Ubuntu services.
`scripts/precheck.sh` catches local errors quickly, but it is not the CI
verdict. See steps 3 and 5.

  This section used to say "never wait on GitHub CI — gate locally and let CI
  confirm afterwards", and steps 3 and 4 below told you to run
  `scripts/gates.sh`. The `PreToolUse` hook in `.claude/settings.json` refuses
  that command in every mode, so the instruction could not be followed: every
  iteration hit a blocked hook at the step this skill calls its definition of
  done, and no iteration ever produced a gate verdict at all.

## 0a. This skill needs its own tooling on `main`

`gh pr checkout` puts you on a branch cut before this tooling existed, so
`scripts/precheck.sh`, `scripts/check_mathlib_style.py`, and the edit hook are
all absent there until the tooling commit is on `main` and the PR has been
rebased.

Check first:

```bash
git ls-tree origin/main --name-only scripts/precheck.sh scripts/check_mathlib_style.py
```

Fewer than two lines? Stop: land the tooling PR before running this loop.
Running the checks from another branch's copy works for a one-off dry run but
leaves the branch's own edits ungated, which is the opposite of the point.

## 0. Refuse to start if the tree is dirty

```bash
git status --porcelain
```

Non-empty? **Stop and report.** Do not stash. The previous iteration did not
finish, and a human decides what happens to its work.

## 1. Pick the target

```bash
git fetch origin
python3 scripts/pr_queue.py
```

Treat the rows as candidates. Verify the selected PR's native issue blockers,
actual Git ancestry and overlap with other open PRs before acting. Do not
advance a dependent PR ahead of its predecessor.

If the selected PR is `CONFLICT`, rebase it, resolve, gate, push, and halt.

**Exit code 2 means stop the loop, and it means two different things.** The
script prints which:

- `BLOCKED ON YOU` — every open PR is already gated and reviewed at its current
  head, and is waiting on a human to merge. **Stop the loop** and say so, naming
  the PRs and the count. Do not re-review an unchanged head: the verdict is
  already posted and repeating it costs a full build to say nothing. This is the
  failure mode worth naming out loud, because a loop that reports "nothing to
  do" when the real answer is "eleven PRs need you" has failed silently — the
  two look identical from the outside.
- `QUEUE DRAINED` — there are genuinely no open PRs needing an iteration. Stop
  the loop and say that instead.

Either way the loop ends. It restarts the moment a merge or a new push changes
the queue, and that is the human's cue, not a reason to keep waking up.

## 2. Check out and rebase

```bash
gh pr checkout <N> -R chris-dare-dev/derived-alg-geo-lean || exit 1
git rebase origin/main
```

**The `|| exit 1` is load-bearing.** If the checkout fails, `git rebase
origin/main` rebases whatever branch you happen to be standing on — which is
not the PR, and may be unmerged work. Never run the two as separate steps that
both execute regardless.

`gh pr checkout` fails when the PR's branch is already checked out in another
worktree:

> fatal: 'agent/…' is already used by worktree at '…'

That is not a reason to skip the PR. Find the worktree and run the whole
iteration there instead:

```bash
git worktree list | grep '\[agent/<branch>\]'
```

Two things to check before working in someone else's worktree:

- **It must be clean.** A dirty worktree is unfinished human work — halt and
  report, exactly as in step 0. Never stash it.
- **Its `.lake/packages` is often a symlink to a sibling worktree**, and those
  siblings get deleted. A dangling symlink shows up as a baffling
  `mkdir: .lake/packages: No such file or directory` from `lake build` even
  though `.lake` plainly exists. Check with `ls -la .lake`, and repoint it at
  the main checkout's packages when it dangles:

  For a fresh worktree, use `scripts/seed_worktree_cache.sh --dry-run` to
  inspect a suitable donor. For an existing cache, resolve the actual shared
  package location before repairing the symlink. Never reuse a hard-coded
  path from another machine.

  Only do this once `lean-toolchain` and `lakefile.toml` are identical to
  `origin/main`, which after step 2's rebase they are. Sharing a package set
  across differing pins would be silent corruption, not a repair.

A conflict needs a declaration-level review. Preserve the selected PR's intended
work and current main; do not resolve by a blanket preference for either side.

If the rebase cannot be resolved without guessing at mathematical intent, abort
it (`git rebase --abort`), comment on the PR with the exact conflicting hunks,
and halt. Do not guess.

## 3. Pre-flight locally — this is not the verdict

```bash
scripts/precheck.sh
```

Seconds, not minutes. It runs every gate that needs no Lean build — workflows,
style on this branch's own lines, source-independence, layering, umbrella
coverage, root reachability, coherent families, coverage map, pin, nolints,
roadmap, and the two hook tests — then a **targeted** `lake build` of the
modules the branch changed.

**Do not run `scripts/gates.sh`.** The `PreToolUse` hook refuses it in any
mode, because its `build` gate is the whole-library build that cost a developer
three hours on 2026-08-27. `DAG_ALLOW_LOCAL_BUILD=1` exists for a genuinely
unavailable runner and nothing else; using it is a reportable event, so say so
in the verdict comment if you do.

**What `precheck.sh` cannot tell you**, and what therefore has to come from the
runners in step 5: the library build, all three axiom audits, the
audit-completeness ratchet, `runLinter`/`lint-style`, the warning ratchet, the
emitter and its coverage check, the `exe` sorry sweep, and the `mfc` contract
tooling. A clean precheck is a *cheap* green, not a green.

A failing check is the iteration's work, not a reason to weaken it. Historical
examples include:

- a new public theorem missing from `scripts/StabilityConditionAudit.lean`,
  `scripts/AlgebraicGeometryAudit.lean`, or `scripts/DGCategoryAudit.lean`
  — **CI only**, so read the branch diff for new `theorem`/`def` lines and add
  the records before you push rather than waiting for the PR CI run;
- `check_source_independence.py` rejecting a retired or external source root
  — precheck catches this;
- convention errors the edit hook would have caught had the branch been written
  with it installed — precheck catches these. Fix them; they are one-line fixes.

Never introduce a `sorry` to get a gate green. If the branch already contains
one, that is a `NEEDS REWORK` verdict, not something to work around.

## 4. Review

Run the `mathlib-reviewer` agent over `git diff origin/main...HEAD`. Apply its
`blocker` and `should-fix` findings yourself when they are mechanical — a name
that does not transcribe its statement, a docstring that restates the signature.
Leave anything requiring mathematical judgement for the PR comment.

## 5. Push, and take the verdict from the pull request run

The push is **no longer** the gate run. Since 2026-09-19 `ci.yml` triggers
`push` on `main` alone, so the run that gates this branch is the `pull_request`
one on `ubuntu-latest`: the identical job set, the run branch protection reads,
and over the 195 commits both lanes used to build, the faster of the two
(20.8 min median against 40.2). The pull request is already open by step 1, so
the push below still starts it.

```bash
git push --force-with-lease
gh run list --branch "$(git branch --show-current)" --workflow ci.yml \
  --limit 1 --json databaseId,url --jq '.[0]'
```

Then wait on it:

```bash
gh run watch <databaseId> -R chris-dare-dev/derived-alg-geo-lean --exit-status
gh run view <databaseId> -R chris-dare-dev/derived-alg-geo-lean \
  --json status,conclusion --jq '"\(.status)/\(.conclusion)"'
```

**Read the conclusion, not the exit code.** `gh run watch --exit-status` exits
**0 on a cancelled run**, and cancellation is the normal outcome here: `ci.yml`'s
concurrency group cancels the in-flight run on the next push to the same ref, so
every `--force-with-lease` in step 5 kills the run before it. Observed
2026-09-16 on run 35158669480 — the watcher returned 0 and the run's conclusion
was `cancelled`. Only `completed/success` is green.

**Bound the wait.** Capacity and queue delay vary. If the run has not *started*
within about ten minutes, stop waiting: post the verdict comment with the run
URL and the precheck result, leave the PR as it is, and halt. The next
iteration re-reads the queue and will find the finished run.

To gather supplemental self-hosted Ubuntu evidence without pushing again:

```bash
gh workflow run ci.yml --ref "$(git branch --show-current)"
```

This manual `workflow_dispatch` run does not replace the required PR `ci`
check. If that check was cancelled, obtain a new `pull_request` run for the
current head and verify its completed conclusion before treating the PR as
green. Then report:

```bash
gh pr comment <N> -R chris-dare-dev/derived-alg-geo-lean --body "<verdict>"
```

The verdict comment states, in this order: the head commit it was written
against; that `scripts/precheck.sh` was clean locally (naming it, not
"the gates"); the CI run URL and its conclusion, or that the run was still
queued when the iteration halted; what you fixed; what you left for a human and
why; and the reviewer's verdict with finding counts by severity. If you used
`DAG_ALLOW_LOCAL_BUILD=1` for anything, say so here.

Never write "gates pass" on the strength of a local run. Precheck does not run
the full library build or the expensive audit and emitter checks.

If the PR is a draft, **the CI run concluded green**, and the reviewer said
`MERGE`:

```bash
gh pr ready <N> -R chris-dare-dev/derived-alg-geo-lean
```

A queued or failed run is not a green run. Leave the PR in draft and say why.

## 6. Halt

Return to a detached-free clean state on `origin/main`. If the iteration ran in
another worktree, leave that worktree on its own branch and clean — do not
switch it to `main`, since a human may be using it. Report three lines: the
PR touched, its new state, and the one thing a human must decide.

**Do not merge. Do not start the next PR.** The next iteration re-reads the
PRs, dependencies and main, since a merge or new push can change eligibility.
