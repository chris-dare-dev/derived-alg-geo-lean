---
name: land-pr
description: Run one unattended landing iteration — take the base of the open PR stack, rebase it, pre-flight it with scripts/precheck.sh, review it, push for the CI gate verdict, mark it ready, then stop. Never merges. Pair with /loop.
---

# One landing iteration

The open PR queue, not the issue tracker, is where this repository's work is
stuck. This is **one** iteration against that queue and it **halts** before the
merge. Merging is a human action, always.

When called by a bounded loop manifest, the controller's OpenSpec change and
review ledger remain authoritative. Landing may act only on the reviewed head;
the three adversarial lenses plus `mathlib-reviewer` must already have been
recorded for the frozen chunk, and the controller's maximum of three
review/improve rounds still applies. This skill's normal one-PR stop behavior
is unchanged.

## What the queue actually is

Every open PR is based on `main`, but they are a **cumulative stack**: each
slice contains all of its predecessors, so diffs run +65, +134, +168, … +2925
along one chain. Two consequences drive everything below:

- **Land the base, not the tip.** Merging the tip would land 26 issues in one
  unreviewable commit. Merging the base makes the next PR's diff collapse to its
  own slice.
- **The queue is CI-bound, not review-bound.** One 90-minute build job serialises
  28 PRs, and there is no way around that: the verdict comes from the
  self-hosted Windows runners and nowhere else. What you *can* do locally is
  fail fast — `scripts/precheck.sh` answers the cheap half in seconds, so a
  typo never costs a 90-minute round trip. It is not a verdict. See step 3.

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

Take the **first row**. The ranking already encodes the landing order: `READY`
before `GATE` before `FIX` before `CONFLICT`, then smallest diff first.

Never take a row out of order to find easier work — the stack means a later PR's
diff is a lie until its predecessors land.

If the first row is `CONFLICT`, that is the iteration: rebase it, resolve, gate,
push, and halt.

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

**This repository uses ~22 git worktrees**, and `gh pr checkout` fails outright
when the PR's branch is checked out in one of them:

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

  ```bash
  ls -d "$(readlink .lake/packages)" 2>/dev/null || {
    rm .lake/packages
    ln -s /Users/chris.dare/Personal/SourceCode/coherent-sheaves-lean/.lake/packages .lake/packages
  }
  ```

  Only do this once `lean-toolchain` and `lakefile.toml` are identical to
  `origin/main`, which after step 2's rebase they are. Sharing a package set
  across differing pins would be silent corruption, not a repair.

A conflict here is normal for a stacked queue and is your work to resolve. Resolve
it in favour of `origin/main` for anything outside this slice's own leaf path —
a stacked branch carrying a stale copy of an earlier slice is the usual cause.

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

A failing check is the iteration's work, not a reason to weaken it. The usual
failures on this queue, in order of frequency:

- a new public theorem missing from `scripts/StabilityConditionAudit.lean`,
  `scripts/AlgebraicGeometryAudit.lean`, or `scripts/DGCategoryAudit.lean`
  — **CI only**, so read the branch diff for new `theorem`/`def` lines and add
  the records before you push rather than learning it 90 minutes later;
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

**Bound the wait.** One build job serialises the whole queue, so a run can sit
queued for longer than this iteration is worth. If the run has not *started*
within about ten minutes, stop waiting: post the verdict comment with the run
URL and the precheck result, leave the PR as it is, and halt. The next
iteration re-reads the queue and will find the finished run.

To re-run the gate without pushing again — after a label change, or when a run
was cancelled by the concurrency group:

```bash
gh workflow run ci.yml --ref "$(git branch --show-current)"
```

Then report:

```bash
gh pr comment <N> -R chris-dare-dev/derived-alg-geo-lean --body "<verdict>"
```

The verdict comment states, in this order: the head commit it was written
against; that `scripts/precheck.sh` was clean locally (naming it, not
"the gates"); the CI run URL and its conclusion, or that the run was still
queued when the iteration halted; what you fixed; what you left for a human and
why; and the reviewer's verdict with finding counts by severity. If you used
`DAG_ALLOW_LOCAL_BUILD=1` for anything, say so here.

Never write "gates pass" on the strength of a local run. Precheck is fifteen of
the thirty-odd gates and none of the expensive ones.

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
queue, which is the point: once a human merges the base, the rest of the stack
shrinks and the ranking changes underneath you.
