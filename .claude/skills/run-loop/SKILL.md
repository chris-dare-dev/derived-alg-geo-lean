---
name: run-loop
description: Work GitHub issues or a milestone to merged pull requests without stopping for the owner. Research each issue, build it, pass four independent reviewers, merge on green CI, and launch independent R&D after a terminal three-round attempt.
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
5. A `research` label is a triage signal, not proof that the research remains
   open. Compare the issue's stated research criterion with its comments and
   recorded findings. If the criterion is complete and the label is the sole
   preflight blocker, reconcile only that stale label when the active run
   authorization or an explicit owner direction permits it; record the evidence
   and rerun preflight. If label changes are not authorized, continue other
   queued work rather than stopping the run. Keep unresolved research findings
   blocking.
6. Work an epic through its open child issues. If it has none, work its next
   well-defined slice as a progress PR.
7. The run ends when the queue is empty. For a milestone, look once more for
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
   The plan opens the PR description. Before implementation, post the plan
   and frozen issue/acceptance scope as a marked objective comment on the
   issue. Give it a stable objective ID and keep using that ID across
   worktrees, branches, PRs, research and successor attempts. Check earlier
   marked comments for overlapping scope; renaming a slice does not create
   a new objective. Begin each record with
   `<!-- run-loop-objective: <repo>#<issue>/<stable-id> -->`, where the
   stable ID is fixed in the first comment, not regenerated from later edits.
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
3. **Review.** Commit, then reserve a round in a marked issue comment under
   the same objective ID, including attempt and round numbers, exact commit
   and base, before dispatching four reviewers in parallel on that commit.
   A partial or abandoned panel consumes its reserved slot. On a session
   handoff, finish missing roles on that same commit and slot; never reuse
   the reservation for a changed PR-content commit.
   Each is an independent agent following its file in `.claude/agents/`:
   `mathematics-adversary`, `repository-boundary-adversary`,
   `abstraction-adversary` and `mathlib-reviewer`.
   - Give each one the issue, the plan, the commit and its diff against
     `origin/main`. Never give one reviewer another's verdict.
   - Each review ends `Reviewed commit: <sha>` and
     `Close: PASS | PASS_WITH_LIFT | NEEDS_CHANGES | BLOCKED`.
   - Append each complete verbatim review and outcome in marked issue
     comments, linked from the PR description. A missing role stays visibly
     missing; do not paraphrase it into a pass.
   - If all four pass on the same commit, publish. Put any lift under
     follow-ups in the PR description.
   - Otherwise fix what they found, commit, and put the new commit through all
     four again.
   - A frozen implementation attempt gets at most three rounds. After the
     third unsuccessful round, freeze that attempt and start the research
     handoff below. A deterministic required-check failure attributable to
     reviewed PR content on the third reviewed commit is also terminal when
     repair would change that content.
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
   - If a check fails, classify it on the exact PR head. Any repair changing
     PR content, including Lean, scripts, documentation or configuration,
     goes through all four reviewers and reserves the next round of the same
     attempt before a push. A deterministic required-check failure
     attributable to reviewed PR content on the third reviewed commit freezes
     that attempt when repair would change the content; do not make a fourth
     PR-content revision. Rerunning a transient or unrelated check without
     changing reviewed content consumes no review round.
   - When GitHub reports the branch out of date, merge `origin/main` into it and
     push. Never rebase a pushed branch. A conflict-free base refresh needs no
     new panel only after recording that the PR's contribution diff is
     byte-identical and the base did not change relevant imports, pins or
     reviewed behavior. A conflict in the PR's own changes, a changed
     contribution diff or uncertain relevance requires another reserved
     four-role round. This exception does not cover a source repair.
   - Immediately before `gh pr merge <n> --squash`, verify the live PR head is
     the exact reviewed commit or a recorded content-identical base refresh,
     and every required check succeeded on that live head. Never pass
     `--admin`.
   - Remove the worktree and take the next issue. For a progress PR, the next
     item is the next slice of the same issue, until its definition of done is
     met.

## Research after an exhausted attempt

Start this handoff when three reserved implementation-review rounds end without
a pass, or a deterministic required-check failure attributable to reviewed PR
content on the third reviewed commit would require a content-changing repair.

Freeze the failed attempt immediately:
- If a PR exists, mark it as a draft (`gh pr ready --undo`) with the open
  findings in its description. If no PR exists, preserve the local branch and
  record its findings on the issue, whether or not the code is worth keeping.
- Record the exact issue and frozen scope, base and final head SHAs, every
  allocated round and verbatim review, required-check evidence, unresolved
  findings, and tool, documentation, stale-state and reviewer friction. Post
  the handoff under the stable objective ID in an issue comment and mirror it
  in the draft PR description if one exists. Identify any unavailable
  transcript explicitly; do not reconstruct it as a quotation. Preserve the
  failed branch and the existing PR.
- **Immediately dispatch a separate read-only R&D examination** with that
  handoff. Give the researcher the original acceptance criteria, all available
  failed evidence and the live base. Ask for the cause, at least two plausible
  approaches (or a reason only one survives), a changed strategy, bounded
  probes, inherited obligations and a way to falsify the proposal. Research
  may use scratch probes but must not revise the frozen branch.
- Have a reviewer distinct from both the researcher and the proposed
  implementer independently assess the exact research report. The reviewer
  checks that it explains the failure, preserves the entire known history,
  changes the method materially, stays within the original issue/scope, and
  gives a testable acceptance path. Post the report verbatim as a PR or issue
  comment, calculate its SHA-256 from the exact UTF-8 text, and record that
  digest, reviewer identity, verdict and reasons in the handoff. If the report
  changes, obtain a review of the new digest. A rejected report is revised as
  research, never as a fourth implementation-review round.
- If the independent review accepts a changed strategy and the full failed
  review inventory is available, inspect all marked issue comments and PRs
  under the objective ID, account for every reserved and incomplete round,
  and record a successor
  **attempt under the same issue and frozen objective**, inheriting every
  finding. Keep the failed attempt terminal. Each successor has at most three
  implementation-review rounds; across the objective allow at most two recovery
  episodes and nine allocated rounds total. A renamed branch, PR, worktree or
  chunk is not a new objective. The accepted plan, complete history, recorded
  admission and remaining allowance together permit successor implementation.
  The research verdict alone does not authorize a push, PR readiness or merge:
  the successor still needs its own four-role same-commit pass and required CI.
  If the history is incomplete or
  the strategy merely repairs the last finding, continue research or park;
  do not claim a new attempt was admitted.
- If research finds no viable changed strategy, records a false acceptance
  criterion, or exhausts the bounded recovery allowance, record that terminal
  decision and take the next independent issue. Keep dependent issues waiting.

If research establishes that the issue's definition of done is false before
any implementation round, record that finding with the available evidence;
do not invent a failed source commit, PR or review allocation. If the owner
has withdrawn an action needed to continue, preserve the available local
handoff, respect the remaining mutation grants and take independent work.

Marked issue comments are the shared issue-first recovery record; PR
descriptions mirror their current status. This is an agent-enforced protocol,
not a tamper-proof controller. If posting or reading that record fails, do not
dispatch or admit a round. Check the live comment/PR mutation grants before
posting or drafting; if the owner has withdrawn one, retain a local handoff
and work only within the remaining grants. The legacy manifest controller has
its own ledger and rules in
`docs/architecture/loop-recovery.md`. Neither path may silently adopt the
other's authority or reset its review count. On a session handoff, resume an
unfinished research action from the recorded state before taking another
dependent slice. Include the research outcome in the final report.

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

- Do not change the loop's own tooling and instructions during issue proof
  work unless the owner explicitly asks for loop engineering. That
  means `.claude/` (except `.claude/roadmap/`), `.agents/`, `.codex/`,
  `.github/`, `openspec/`, `AGENTS.md`, `CLAUDE.md`, and `scripts/` (except the
  audit and census records). If the tooling gets in your way, work around it or
  park the issue, and describe the problem in the final report.
- An issue about the loop itself (its controller, protocol or instructions) is
  not loop work unless the owner put it in the queue.
- Do not create controller manifests or controller review ledgers, and do not
  run `scripts/loop_engine.py` for issue-first work. The marked issue comments
  and PR description carry the issue-first record.

## When to stop

Stop only when:
1. You need something only the owner has: a password, a token, `sudo`, 2FA.
2. Every issue left in the queue needs an action the owner has withdrawn, or a
   bypassed check.
3. The queue is empty, including research handoffs still awaiting their
   independent plan review or terminal disposition.

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
