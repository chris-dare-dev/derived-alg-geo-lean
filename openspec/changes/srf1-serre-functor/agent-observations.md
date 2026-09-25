# Agent Observations

## 2026-09-23 — SRF1 #897 read-only preflight

- `python3 scripts/loop_engine.py validate --spec .claude/loop-specs/srf1-897-full-faithfulness.yaml` passed. The manifest selected one issue, four independent reviewers, and a three-round cap.
- The first read-only preflight authenticated `chris-dare-dev`, found branch protection and OpenSpec CLI validation ready, then failed because the worktree head `3de1ce62a72702e7dddda47b0626c2f31645e18c` did not contain the newer `origin/main` head `a3d0461fdd807cc919b6962dfe1c972b42415903`, and because issue #897 carried the `blocked` label.
- After rebasing the plan branch onto the fetched `origin/main`, the second read-only preflight passed authentication, branch protection, and OpenSpec CLI validation. It failed only with `issue #897 has ineligible labels: blocked`.
- A final repeat on `HEAD`/`origin/main` `a3d0461f`, after the last OpenSpec wording edits, produced the same one-failure result and again passed the OpenSpec CLI check. The manifest was set back to `enabled: false` immediately afterward.
- GitHub issue reads showed #895 and #896 are closed and #897 remains open. The blocker label still prevents controller eligibility; no issue metadata was changed.
- A read-only GitHub contents request returned HTTP 404 for `.claude/loop-authority.yaml`. Under the loop policy, no branch-authored manifest can grant push, PR, or merge authority without an owner-controlled grant on `main`.
- No GitHub mutation occurred during either preflight. The manifest is now `enabled: false`; it requests only branch push, PR creation, and merge for completion, with comments, direct issue closure, self-approval, auto-merge, and administrator merge disabled.
- At that time, enablement required resolving the `blocked` label, establishing the owner-controlled provider grant on `main`, and rerunning validation plus live preflight from a branch containing the then-current `origin/main`; the later status is recorded below.

## 2026-09-23 — resumed after explicit authorization

- Re-read the live dependency issues: #895 and #896 are closed; #897's body lists them as its blockers. Removed only #897's stale `blocked` label. #898 and #899 retain their `blocked` labels because their listed predecessors remain open.
- Refreshed and rebased the run branch onto `origin/main` at `8351baf8098d3f4f019ea05e58c252e3d6e4193a`. OpenSpec strict validation and manifest validation pass.
- A fresh read-only preflight now passes authentication, base-branch protection, OpenSpec CLI validation, issue eligibility, and repository gates. The manifest is enabled for local ledger and implementation work; provider actions remain denied until the owner grant is merged to `main`. Preflight made no provider mutation.
- Updated the #897 manifest to request the controller-derived predecessor attestation needed by #898. This requires the `comment_issue` capability as well as `push_branch`, `create_pr`, and `merge_pr`; the owner grant proposal includes only those four actions. It remains off `main` until its owner-reviewed PR is merged.
