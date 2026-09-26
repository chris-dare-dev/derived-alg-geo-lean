---
name: run-loop
description: Work GitHub issues or a milestone to merged pull requests without stopping for the owner. Research each issue, build it, pass four independent reviewers, merge on green CI, and go straight on to the next.
---

# Run loop

The owner gives you GitHub issues, or a milestone, and is not watching. Work
every one to a merged pull request. The issue body is the specification, and
your own research fills in the rest. Four independent reviewers check the work.
The owner reads your PRs and your final report and nothing else. So anything you
would ask them, decide yourself, and write the decision down.

## The queue

1. Collect the issues: the ones named, or the milestone's open issues
   (`gh issue list --milestone "<title>" --state open`). Order them by the
   dependencies their bodies and GitHub links state, then by number.
2. Work them in that order. When a PR merges, start the next issue at once.
   Never report "the next lane is …" and wait: the queue already says what is
   next.
3. Skip an issue, and note why for the final report, when it is closed, already
   has someone else's open PR, or depends on an open issue that is not in the
   queue. An issue that depends on a queued issue waits for that issue's merge;
   work the others meanwhile.
4. A `blocked` label is stale when every blocker the body names is closed. Work
   the issue, and say so in its PR.
5. Work an epic through its open child issues. If it has none, work its next
   well-defined slice as a progress PR.
6. The run ends when the queue is empty. For a milestone, look once more for
   issues added while you worked.

While one PR waits on CI you may start the next issue in its own worktree. Keep
no more than two issues in flight.

## Each issue

1. **Research.** Read:
   - the issue, its comments and the issues it links;
   - the code it names;
   - the pinned Mathlib around it (`.lake/packages/mathlib`);
   - any source it cites.

   When the issue introduces a new concept, also run the altitude and
   hypothesis-elimination scouts from `.claude/agents/`. They advise and never
   block. Then write a short plan: what "done" means, what you will build and
   where it lives, what you considered and rejected, and what you will not do.
   The plan opens the PR description.
2. **Build.**
   - Branch `agent/<issue>-<slug>` from the latest `origin/main`, in its own
     worktree, and seed that worktree's cache with
     `scripts/seed_worktree_cache.sh`.
   - Implement by the rules in `CLAUDE.md`: placement, audits, umbrellas, and no
     `sorry`, `admit` or new axioms.
   - Check with targeted builds
     (`LEAN_NUM_THREADS=2 ~/.elan/bin/lake build <Module>`) and with
     `scripts/precheck.sh`. `CLAUDE.md` says how to set up its Python
     environment.
   - If the issue has an entry under `.claude/roadmap/`, advance it in the same
     change. CI's `roadmap` job requires this.
3. **Review.** Commit, then dispatch four reviewers in parallel on that commit.
   Each is an independent agent following its file in `.claude/agents/`:
   `mathematics-adversary`, `repository-boundary-adversary`,
   `abstraction-adversary` and `mathlib-reviewer`.
   - Give each one the issue, the plan, the commit and its diff against
     `origin/main`. Never give one reviewer another's verdict.
   - Each review ends `Reviewed commit: <sha>` and
     `Close: PASS | PASS_WITH_LIFT | NEEDS_CHANGES | BLOCKED`.
   - If all four pass on the same commit, publish. Put any lift under
     follow-ups in the PR description.
   - Otherwise fix what they found, commit, and put the new commit through all
     four again.
   - A PR gets at most three rounds. After the third, park it.
   - If a reviewer returns nothing, dispatch that role again on the same
     commit.
   - Never put your own reading of the diff in place of a reviewer's verdict.
4. **Publish.** Push the branch and open the PR ready for review, not as a
   draft. The description holds:
   - the plan;
   - what changed;
   - every decision you made, and why;
   - each reviewer's verdict with the reviewed commit and the round count;
   - follow-ups;
   - `Closes #<n>`. Use `Progress toward #<n>` instead when the definition of
     done needs more than one PR.
5. **Merge.**
   - Wait for the required checks.
   - If a check fails, fix it and push. A fix that changes the PR's Lean source
     goes back through the four reviewers, and counts as a round.
   - When GitHub reports the branch out of date, merge `origin/main` into it and
     push. Never rebase a pushed branch. That merge needs no new review, unless
     you had to resolve a conflict inside the PR's own changes.
   - Once every required check is green, run `gh pr merge <n> --squash`. Never
     pass `--admin`.
   - Remove the worktree and take the next issue. For a progress PR, the next
     item is the next slice of the same issue, until its definition of done is
     met.

## Park instead of stopping

An issue cannot be finished when any of these happens:
- three review rounds end without a pass;
- a required check still fails after three honest attempts to fix it;
- a research pass confirms the definition of done is false as written;
- it needs an action the owner has withdrawn (see "What you may do").

Then park it:
- Mark its PR as a draft (`gh pr ready --undo`) with the open findings in the
  description. If no code is worth keeping, comment on the issue with what you
  found.
- Add it to the final report.
- Take the next issue.

Never re-chunk, rename or restart an issue to get a fresh review budget.

## What you may do

The request that started the run authorizes these actions for the issues in the
queue:
- pushing `agent/*` branches;
- opening, updating and drafting your own pull requests;
- commenting on the queue's issues and on your own PRs;
- merging your own PRs once every required check passes;
- closing issues through those merges.

The owner withdraws any of these by setting its grant to `false` in
`.claude/loop-authority.yaml` on `main`. For example, `merge_pr: false` means
you open the PR and leave the merge to them.

Never:
- push to `main`, or force-push a shared branch;
- merge with `--admin`;
- change branch protection or repository settings;
- skip or disable a required check;
- edit `.claude/loop-authority.yaml`.

## Stay on the issues

- Do not change the loop's own tooling and instructions during a run. That
  means `.claude/` (except `.claude/roadmap/`), `.agents/`, `.codex/`,
  `.github/`, `openspec/`, `AGENTS.md`, `CLAUDE.md`, and `scripts/` (except the
  audit and census records). If the tooling gets in your way, work around it or
  park the issue, and describe the problem in the final report.
- An issue about the loop itself (its controller, protocol or instructions) is
  not loop work unless the owner put it in the queue.
- Do not create OpenSpec changes, loop manifests or review ledgers, and do not
  run `scripts/loop_engine.py`. The PR description is the record.

## When to stop

Stop only when:
1. You need something only the owner has: a password, a token, `sudo`, 2FA.
2. Every issue left in the queue needs an action the owner has withdrawn, or a
   bypassed check.
3. The queue is empty.

Everything else is yours to decide. That includes ambiguity, a stale label or
path, an unrelated failing check, `main` moving, reviewers who disagree, and a
slow CI run. Take the smallest reading that meets the definition of done, write
it in the PR, and continue.

Do not ask the owner questions during a run. In Codex, do not call
`request_user_input_async` and do not mark the goal blocked while issues remain.
In Claude Code, do not use `AskUserQuestion`. If the runtime ends your turn with
work left — a Codex goal continuing, a heartbeat, a background agent reporting
back — pick up from the queue.

## Final report

When the queue is empty, report once. Post it as your final message and, when
the milestone has a tracking issue, as a comment on that issue. Cover:
- each issue: its PR, whether it merged or was parked, its review rounds, and
  the decisions made;
- each parked issue, with its open findings;
- anything in the tooling that got in the way.
