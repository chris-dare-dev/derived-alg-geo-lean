# AUT1-6 loop-engineering record

This note records repository facts that affected the bounded run for #927.
It is operational guidance, not a mathematical source of truth.

## Verified inconsistencies

- The issue is still open and carries the `blocked` label even though its
  named blockers #922 and #923 are closed.  It also carries `research`, which
  the controller treats as ineligible even though the remaining work is an
  acceptance pass.
- The implementation PR for #927 (#1175) merged on 2026-09-12 into the stacked
  branch `agent/stability-orbit-spaces`, not the repository default branch.
  Its `Closes #927` text therefore did not close the GitHub issue.  The merged
  proper-discontinuity module and audit are nevertheless present on `main`.
- The cutover ledger previously said that no part of #927 was implemented;
  that statement described neither the current code nor the stacked-branch
  merge behavior.

## Practices that waste agent time

- `openspec list --all` is not a valid command for this CLI; use
  `openspec list` for active changes and `openspec list --specs` for capability
  inventory.
- The repository's old notes mention `scripts/precheck.py`; the available
  entrypoint is `scripts/precheck.sh`, followed by a named `lake build` target.
- On Windows, `scripts/seed_worktree_cache.sh --dry-run` can misread a
  PowerShell-created worktree as outside Git even while native `git` works.
  Use the native Git worktree metadata and a validated cache copy/junction
  rather than recreating the worktree.
- A cold package cache can make one named target compile hundreds of Mathlib
  package modules.  Keep `LEAN_NUM_THREADS=2`, do not start concurrent Lake
  builds, and distinguish cache warming from a whole-repository build.
- Some reviewer final messages can be empty; the ledger and independent
  verification, not message presence alone, are the evidence of review.
- Editing OpenSpec checkboxes changes its digest; after any planning edit,
  initialize a fresh ledger instead of reusing an earlier state.
- The local precheck reports a workflow failure when `actionlint` is absent;
  `SKIP_ACTIONLINT=1 bash scripts/precheck.sh --no-build` lets the remaining
  local gates run, but the self-hosted CI workflow check is still the verdict.
- The loop-controller capability spec says a run has two or three issues, while
  the current validator accepts `min_issues: 1`.  This user-directed run keeps
  one issue because #927 is the only open issue in its AUT1 milestone; no
  unrelated issue is added merely to satisfy the stale batch-size prose.
