# Design

## Context

OpenSpec is intentionally the planning layer: its standard `spec-driven`
workflow produces `proposal.md`, delta specs, `design.md`, and `tasks.md` and
keeps those artifacts readable in Git. It does not model provider credentials,
issue eligibility, review identity, or an unattended mutation policy. Those
concerns belong to a small repository-local controller.

## Goals / Non-Goals

### Goals

- Make the scope of a two-to-three-issue run explicit and hashable.
- Freeze each implementation chunk to an issue, OpenSpec change, file list,
  acceptance statements, and reviewed commit.
- Require independent adversarial lenses before adjudication.
- Make the third failed round a terminal stop rather than a fourth attempt.
- Make remote mutations opt-in per action and make code-issue closure require a
  merged pull request.

### Non-Goals

- Replacing GitHub branch protection, CI, or human mathematical judgment.
- Claiming that a passing review proves a theorem or that a green build proves
  the intended mathematical statement.
- Automatically merging or closing issues by default.
- Making OpenSpec artifacts carry secrets or provider tokens.

## Decisions

1. **OpenSpec plus a run manifest.** OpenSpec artifacts hold the intended
   behavior and implementation plan. A tracked YAML manifest references the
   OpenSpec change and separately declares issues, action capabilities, and
   review roles. This avoids forcing provider control data into a behavioral
   requirement document.
2. **Portable structural validation first.** The controller validates the
   referenced OpenSpec files without requiring Node on Lean-only runners. When
   the OpenSpec CLI is installed, a manifest may require or advise a strict CLI
   validation pass.
3. **Ledger state is ephemeral and hash-bound.** `.loop-runs/` records reviewer
   evidence locally and is ignored by Git. It stores the run-manifest digest and
   OpenSpec-artifact digest, so a changed plan cannot approve an old review.
4. **Provider actions are explicit subcommands.** Comments, closure, push,
   PR creation, approval, and merge each require a corresponding boolean in the
   manifest. The controller uses argument arrays, never shell interpolation.
5. **Review rounds are per frozen chunk.** All required reviewers must review
   the same commit before adjudication. A new commit starts the next round; the
   cap is three, and scope cannot be re-chunked to evade it.

## Review Panel

- `mathematics-adversary`: checks source equations, quantifiers, hypotheses,
  constructions, and counterexamples.
- `repository-boundary-adversary`: checks imports, trust boundaries, pins,
  generated code, sorry/axiom policy, and the actual gate surface.
- `abstraction-adversary`: checks canonical ownership, projections/comparison
  maps, instance diamonds, reuse by independent consumers, and abstraction
  churn.
- `mathlib-reviewer`: checks Lean/mathlib API and style compatibility. It is not
  a substitute for the mathematical adversary.

## Risks / Trade-offs

- **The manifest can be stale** → preflight checks the clean base, live issue
  state, dependencies, branch/PR collisions, provider identity, and roadmap.
- **OpenSpec CLI is absent on a runner** → structural validation remains
  portable; `cli-required` is opt-in and fails closed.
- **Review churn can consume the run** → each chunk stops at three rounds and
  is recorded as blocked for later human triage.
- **A user enables too many mutations** → each action remains named, logged by
  the command output, and merge defaults to false.

## Migration Plan

1. Install OpenSpec locally and initialize only its repository structure.
2. Commit the controller change and the disabled pilot manifest.
3. Run the local validation/tests and inspect the first preflight failures.
4. Enable a pilot only after the issue set, dependencies, branch protection,
   and the action policy have been reviewed.

## Open Questions

- Whether the final pilot should use stack mode with explicit merge authority or
  be split into independent issue batches remains a repository-owner decision.
