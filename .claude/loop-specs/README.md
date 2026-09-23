# Loop manifests

A manifest is the plan for one unattended run: which issues it takes, how each
is cut into frozen chunks, which files each chunk may touch, what "done" means
for it, and who reviews it. A run writes its manifest on the issue's
`agent/<slug>` branch, and the manifest ships in that PR. Nothing has to merge
to `main` before the work starts.

- The issue body is the specification. A chunk's `acceptance` restates the
  issue's definition of done.
- `openspec/changes/<name>/` is optional for a single issue and expected for a
  multi-issue batch. It holds the proposal, requirements and scenarios, design,
  and tasks.
- `.loop-runs/` holds local, ignored review ledgers for frozen commits.

## A minimal single-issue manifest

Omitted keys take their defaults: `limits.min_issues` 1,
`limits.max_issues` 3, `openspec` absent, `requirements` empty, and
`mutations` absent (standing authority applies unnarrowed).

```yaml
schema: derived-alg-geo-lean.loop-run/v1
id: rou1-919-generation-time
repository: chris-dare-dev/derived-alg-geo-lean
actor: chris-dare-dev
remote: origin
base_branch: main
base_ref: origin/main
mode: independent
enabled: true
roadmap_gate: required
limits:
  max_review_rounds_per_chunk: 3
review:
  independent: true
  reviewers: [mathematics-adversary, repository-boundary-adversary, abstraction-adversary, mathlib-reviewer]
  advisors: [altitude-scout, hypothesis-elimination-scout]
runner:
  required_checks: [ci]
closure:
  code_issue: pr_merge_keyword
  allow_non_pr: false
issues:
  - number: 919
    slug: rou1-919-generation-time
    chunks:
      - id: rou1-919-generation-time
        scope: "<one sentence: what this chunk proves, and what it explicitly does not>"
        files:
          - "DerivedAlgGeo/<leaf the issue names>"
          - "DerivedAlgGeo/<its umbrella>"
          - "scripts/<the audit slice for its declarations>"
          - docs/architecture/generalization-backlog.md
        acceptance:
          - "<each definition-of-done item from the issue, restated as a checkable statement>"
```

## Provider authority

Provider actions each need a grant: comments, pushes, PR creation, marking
ready, follow-up issues, issue closure, approval, and merge. The controller
honours two sources. It reads both from the repository's default branch through
the GitHub API, never from a local ref (a remote-tracking ref is locally
writable), so a work branch cannot grant itself anything:

- `.claude/loop-authority.yaml` on `main` is the owner's standing grant. A
  manifest's `mutations` may set a key to `false` to narrow it, but can never
  widen it. Without the file, nothing is granted, and a run stops at its first
  provider action (stop reason 1). An explicit `false` in the file revokes that
  action for every run; it is the owner's kill switch.
- The manifests the owner reviewed through planning PRs before this
  protocol are listed by content digest in `LEGACY_REVIEWED_MANIFESTS` in the
  controller. They keep their own explicit `mutations` and merge, closure and
  eligibility policies, subject to the kill switch, and only while the
  selected issue is open: the controller refuses them at ledger init and PR
  creation for a closed issue. A manifest merged later through a work PR is not
  on that list and confers nothing by being merged.

A manifest that is not on the legacy list is branch-authored. Validation and
the actions hold it to these limits:

- `base_ref` must be `<remote>/<base_branch>`;
- no administrator merge, force-push, closure without a merged PR, epic opt-in,
  or roadmap gate weaker than `required`;
- no chunk file or lift target, and no changed path at publication, under the
  run's own authority, gates or instructions (`PROTECTED_PATH_PREFIXES`):
  - all of `.claude/`, except the run's own manifest and the roadmap data
    (`.claude/roadmap/*.yaml`, which RM-08 in the required `ci` check requires
    a closing PR to advance);
  - `.agents/`, `.codex/`, `.mcp.json` and `CLAUDE.local.md`;
  - every `CLAUDE.md`, `AGENTS.md`, `.gitattributes`, `.gitmodules` and
    `.gitignore`, at any depth;
  - `.github/`;
  - all of `scripts/` except the audit and census records
    (`scripts/*Audit.lean`, `scripts/*Census.lean`, and the Lean records under
    `scripts/*Audit/`), so the gates, hooks, baselines and controller are
    covered;
  - `exe/`, `registry/` and `DerivedAlgGeoSweep.lean`;
  - the pins (`lakefile.toml`, `lean-toolchain`, `lake-manifest.json`,
    `pins.json`);
  - all of `openspec/` except the run's own change directory, so other runs'
    contracts and the accepted specs are covered;
  - `docs/architecture/loop-recovery.md`.

  Paths are compared after collapsing `./`, `//` and `\`, and case-insensitively;
  a path with a `.` or `..` segment is refused. A run may also not add a
  symlink or submodule anywhere, because a symlink writes through to its
  target. Those paths change only through owner-reviewed PRs.

**Expected owner stops.** Some ordinary maths work needs a protected path. Such
a chunk parks under stop reason 1 and files a follow-up issue naming the exact
change, instead of working around the rule. These are the known cases:
- a public rename needs its historical name restated in
  `exe/RestateHistoricalNames.lean`;
- a gate baseline moves (`scripts/single_instantiation_baseline.txt`,
  `scripts/warning-baseline.json`, `scripts/style-baseline.json`,
  `scripts/nolints.json` or `scripts/audit_missing_baseline.txt`);
- a reference note under `.claude/references/` changes;
- a pin is bumped.

The owner creates and edits that file; a run never does. Its shape:

```yaml
schema: derived-alg-geo-lean.loop-authority/v1
mutations:            # each key defaults to false when omitted
  comment_issue: true
  push_branch: true
  create_pr: true
  ready_pr: true
  create_issue: true  # follow-up issues for deferred findings
  close_issue: true   # still only after a confirmed merged PR
  merge_pr: true      # still only with a passing ledger, green required checks,
                      # and --match-head-commit pinned to the verified head
  approve_pr: false   # branch protection requires no approval; GitHub refuses self-approval
```

## Automatic recovery

For automatic recovery after exhausted review, see
[the recovery protocol](../../docs/architecture/loop-recovery.md).
The optional `recovery` section configures `objective_id`, `implementer`,
`max_episodes` (default 2), `max_total_rounds` (9),
`max_plan_submissions` (2 per episode), `max_elapsed_seconds` (604800), and
`history` entries with `path` and `sha256`. Recovery manifests have exactly
one issue and one chunk. New attempts have at most three rounds, and imported
history and partial panels count toward the cumulative limit. Existing
manifests retain their behavior unless explicitly opted in.

An active supervising agent consumes
`.loop-tools/bin/python scripts/loop_engine.py recovery next --ledger <ledger>`,
dispatches research and independent plan review on exhaustion, and resumes only
after acceptance. No background daemon or routine user approval is involved.
The failed attempt remains preserved and provider permissions remain separate.

## Lift targets and the lift chunk

A reviewer regularly finds that a statement belongs at a higher altitude, in a
file the frozen chunk may not touch. Two manifest keys give that finding a legal
route without a mid-run manifest edit — which would move `digest(spec)` and
invalidate every passed dependency ledger in the run.

```yaml
chunks:
  - id: <chunk-id>
    files:
      - DerivedAlgGeo/<the leaf this chunk implements>
      - docs/architecture/generalization-backlog.md
    lift_targets:
      # ancestor prefixes this chunk's concepts might actually belong to.
      # Declaring one is standing permission, not an open door: the controller
      # refuses a diff here until a reviewer records pass_with_lift naming a
      # path under it.
      - DerivedAlgGeo/<plausible ancestor>
```

### What happens when a reviewer opens one

Authorization keys off the **recorded review**, not the adjudication. The moment
a reviewer records `pass_with_lift --lift-target <path under a declared prefix>`,
that prefix is writable for this ledger. So at adjudication the orchestrator has
a real choice, and both options are legal:

- **`needs_changes`** — implement the lift now. The ancestor is open, the next
  round reviews the widened diff, and it costs one round like any other fix.
  Choose this when the lift is small and the chunk is young.
- **`pass_with_lift`** — ship the chunk as reviewed and carry the lift to
  `docs/architecture/generalization-backlog.md` for a later run. This requires
  no additional revision round; a recovery-mode panel's allocation still counts.
  Choose this when the lift is large, cascading, or would outgrow the issue.

Note the asymmetry: only the second requires the backlog row, because only the
second defers. Adjudication refuses `pass_with_lift` while the target is missing
from the backlog, so a deferred lift cannot be lost.

**Do not pre-declare a separate `<issue>-lift` chunk.** It deadlocks a run that
finds no lifts: `verify_local_chunk_files` refuses a chunk whose diff is empty
("frozen chunk has no committed file changes relative to the protected base"), so
a lift chunk with nothing to implement fails the run rather than being skipped. A
lift too large for the current issue belongs in the backlog and then in the next
manifest, where it is ordinary planned work.

**Choosing `lift_targets` is a mathematical judgement, not a mechanical one.**
Derive them from `docs/architecture/abstraction-tree.md` when you plan the run,
and leave the key absent rather than guessing: an ancestor named wrongly is
standing authorization to edit a file nobody meant to open.

Set up the pinned controller dependencies once in each fresh worktree, then
validate and preflight a manifest from its work branch:

```text
python3 -m venv .loop-tools
.loop-tools/bin/python -m pip install -r scripts/requirements-loop.txt
.loop-tools/bin/python scripts/loop_engine.py validate --spec .claude/loop-specs/<slug>.yaml
.loop-tools/bin/python scripts/loop_engine.py preflight --spec .claude/loop-specs/<slug>.yaml
```

Preflight accepts an uncommitted or branch-committed plan, and any head that
contains `base_ref`. It refuses:
- other uncommitted work;
- a stale branch;
- another branch's open PR for the same issue.

A merged or closed PR on the planned branch name is history, not a collision.
An open one is this run being resumed.

The merge policy defaults to squash with branch deletion; a squash-merged branch
left behind would block the next run that plans the same name. Method,
auto-merge, administrator merge and branch deletion remain explicit settings.
Code issues may only be closed after a confirmed merged pull request.

## Ledgers and moving bases

- A ledger written by this controller records its plan paths and plan-digest
  version 2. Version 2 ignores task checkbox state and `agent-observations.md`,
  so ticking tasks or appending the observation log no longer invalidates a
  review. Ledgers written before this change keep verifying under version 1.
- A passing round covers a later head only when all three of these hold:
  - it carries the same change against the base branch tip GitHub reports
    (such as after a clean rebase onto a moved `main` or a merge of `main`);
  - only the progress records differ, meaning checkbox state in `tasks.md` and
    the change's top-level `agent-observations.md`; the manifest and every
    other plan file are part of the reviewed change;
  - the base did not change a chunk file, a Lean module a chunk file imports
    directly, or `lake-manifest.json`, `lean-toolchain` or `lakefile.toml`.
- Otherwise, one revalidation round with the full panel reopens the pass. A
  revalidation round does not spend `max_review_rounds_per_chunk`, and a
  ledger allows at most two.
