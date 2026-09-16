---
name: formalize-issue
description: Run one unattended formalization iteration — claim a ready GitHub issue, formalize it on a branch, pre-flight it with scripts/precheck.sh, open a PR and take the gate verdict from CI, then stop. Use for hands-off sessions; pair with /loop for repeats.
---

# One formalization iteration

This is **one** iteration and it **halts** at the PR. It never merges, never
pushes to `main`, and never leaves a `sorry` behind. Under `/loop` it will be
re-entered from a clean state, so everything below must be safe to re-run.

Issues live on `chris-dare-dev/derived-alg-geo-lean`.

## 0. Refuse to start if the tree is dirty

```bash
git status --porcelain
```

Non-empty, or the current branch is not `main`? **Stop and report.** Do not
stash, do not commit stray work, do not switch branches over uncommitted
changes. A dirty tree means the previous iteration did not finish; a human
decides what happens to it.

## 1. Claim an issue

```bash
gh issue list -R chris-dare-dev/derived-alg-geo-lean --state open \
  --limit 40 --json number,title,labels,body
```

Pick the **first** eligible issue, preferring the lowest number — the tracker is
ordered by dependency, not priority. Eligible means, in order of preference:

1. labelled `ready`;
2. otherwise unlabelled or plainly-labelled implementation work.

Never eligible: anything labelled `blocked`, `epic`, `type:spike`, or
`research`. Those are coordination or investigation items, not one-sitting
formalizations. Also skip any issue whose named leaf path already exists with
the theorem proved.

**Never eligible, and this is the one that actually bites:** an issue that
already has an open PR or an existing `agent/` branch. At the time of writing,
28 of the 30-odd open implementation issues were already in flight, so an
iteration that skips this check will silently redo finished work. Compute the
exclusion before choosing:

```bash
gh pr list -R chris-dare-dev/derived-alg-geo-lean --state open --limit 200 \
  --json number,headRefName,body \
  --jq '.[] | "\(.headRefName)\t\(.body)"' | grep -oiE '(closes|fixes|resolves) #[0-9]+'
git branch -a --list 'agent/*'
```

If every eligible issue is already claimed, **stop and say so.** The bottleneck
is review, not formalization; report the open-PR count and halt. Do not pick a
claimed issue, and do not invent work.

Most open issues carry no `ready` label today, so do not filter on it with
`--label`; read the labels and decide.

If nothing is ready, stop and say so. Do not invent work.

Post a claim comment so a parallel session does not take the same issue:

```bash
gh issue comment <N> -R chris-dare-dev/derived-alg-geo-lean \
  --body "Claimed by an unattended formalization run at $(date -u +%FT%TZ)."
```

## 2. Branch

```bash
git switch main && git pull --ff-only
git switch -c agent/<short-slug-from-the-issue-title>
```

## 3. Formalize

Read `CLAUDE.md` and `.claude/references/mathlib-style.md` before writing Lean.
The rules that bite most often in unattended runs:

- **No `sorry`, ever** — not even temporarily, not even in a file you intend to
  finish this iteration. The edit hook blocks it. If the proof will not close,
  that is a step-5 outcome, not something to paper over.
- One issue owns one leaf path. Do not refactor an unrelated subsystem because
  you noticed something; note it for step 6 instead.
- Foundational subject modules must remain independent of specialized consumers.
- Export the new leaf through its nearest subsystem umbrella.
- Add every new public theorem to `scripts/AlgebraicGeometryAudit.lean`,
  `scripts/StabilityConditionAudit.lean`, or `scripts/DGCategoryAudit.lean`.
- Write the module docstring and declaration docstrings **as you go**, to the
  standard in the style reference: say why the hypothesis is needed and what the
  proof idea is, not what the signature already says.

The `PostToolUse` hook runs `scripts/check_mathlib_style.py` after every edit
and blocks on convention errors. Fix them immediately; do not batch them.

**Budget the iteration.** If the proof has not closed after roughly 45 minutes
of work, or you are on the third distinct proof strategy, go to step 5 and
report the obstruction. A well-written obstruction report is a successful
iteration. Grinding is not.

## 4. Pre-flight locally — this is not the verdict

```bash
scripts/precheck.sh
```

Seconds, not minutes. It runs every gate that needs no Lean build — workflows,
style on this branch's own lines, source-independence, layering, umbrella
coverage, root reachability, coherent families, coverage map, pin, nolints,
roadmap, and the two hook tests — then a **targeted** `lake build` of the
modules this branch changed, which is where a proof that does not compile shows
up.

**Do not run `scripts/gates.sh`.** The `PreToolUse` hook in
`.claude/settings.json` refuses it in any mode: its `build` gate is the
whole-library build that cost a developer three hours on 2026-08-27. This step
used to say `scripts/gates.sh fast` and then `scripts/gates.sh`, which meant
every unattended iteration stopped dead at a blocked hook here — at the step
the skill calls its definition of done — and no iteration ever got a verdict.
`DAG_ALLOW_LOCAL_BUILD=1` is for a genuinely unavailable runner and nothing
else; using it is a reportable event, so say so in the PR body.

Before pushing, do the one thing precheck cannot do for you: **add every new
public declaration to its audit** (`scripts/AlgebraicGeometryAudit.lean`,
`scripts/StabilityConditionAudit.lean`, `scripts/DGCategoryAudit.lean`). The
audits and the completeness ratchet need the library elaborated, so they run on
the runner only, and a missing record is the most common way an otherwise
finished iteration comes back red.

A failing check is the iteration's work, not a reason to weaken it.

**The verdict comes from the self-hosted Windows runners**, after the push in
step 6. `ci.yml` triggers on `push` to `agent/**`, so the push is the gate run;
for a verdict without pushing, `gh workflow run ci.yml --ref agent/<slug>`.

## 5. If it did not close

Do not open a PR. Do not leave the branch half-committed.

```bash
git switch main
git branch -D agent/<slug>          # only if nothing worth keeping
```

Comment on the issue with: the statement you tried to prove (verbatim Lean), the
strategies attempted, the exact goal state you got stuck on, and what Mathlib
lemma you looked for and could not find. Then **stop the iteration**.

## 6. PR

```bash
git add <only the files this change owns>   # inspect `git status` first
git commit -m "feat: <what was proved>

Closes #<N>."
git push -u origin agent/<slug>
gh pr create -R chris-dare-dev/derived-alg-geo-lean --fill
```

The push started the gate run on the Windows runners. Find it and wait on it:

```bash
gh run list --branch "agent/<slug>" --workflow ci.yml --limit 1 \
  --json databaseId,url --jq '.[0]'
gh run watch <databaseId> -R chris-dare-dev/derived-alg-geo-lean --exit-status
```

**Bound the wait.** One build job serialises the queue. If the run has not
*started* within about ten minutes, stop waiting: say so in the PR body with
the run URL and halt. Do not claim a gate verdict you did not see.

Then run the `mathlib-reviewer` agent on the branch diff and post its findings
as a PR comment. If it returns `NEEDS REWORK`, fix the findings, re-run
`scripts/precheck.sh`, and push again before halting — the point of a hands-off
run is that the PR is reviewable when the human returns, not that it exists.

State the CI conclusion honestly in the PR body: green, red with the failing
step named, or still queued. A clean `scripts/precheck.sh` is fifteen of the
thirty-odd gates and none of the expensive ones; never write it up as "gates
pass".

Finally, if step 3 turned up unrelated work worth doing, file it as its own
issue now.

## 7. Halt

Return to `main`. Report in three lines: the issue closed, the PR URL, and the
reviewer verdict. Do not start another issue.
