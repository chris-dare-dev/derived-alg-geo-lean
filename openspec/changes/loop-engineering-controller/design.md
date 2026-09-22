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
- Make the fifth failed round a terminal stop rather than a sixth attempt.
- Make remote mutations opt-in per action and make code-issue closure require a
  merged pull request. Permit a progress PR only when the frozen chunk and
  manifest explicitly authorize it, and require that PR to avoid closing
  keywords.
- Permit a separately capped successor run only when it is anchored to durable
  controller evidence for a reviewed, merged predecessor run.

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
   manifest. A chunk's `closure` mode is `complete` by default; `progress`
   requires `spec.closure.allow_progress_pr: true`, a non-closing issue
   reference, and no closing keyword. The controller uses argument arrays, never
   shell interpolation.
5. **Review rounds are per frozen chunk.** All required reviewers must review
   the same commit before adjudication. A new commit starts the next round; the
   cap is five, and scope cannot be re-chunked to evade it.
6. **Attested predecessor PRs.** A source manifest may require an
   `attest-pr` controller action before its PR can merge. The action derives a
   machine-readable comment from the passing ledger: source manifest/chunk,
   issue/branch/closure, manifest and OpenSpec digests, cap, and exact reviewed
   PR head. A successor pins that complete tuple together with the source PR
   number and merge commit. Preflight, ledger initialization, and every successor PR action
   query the provider again, require the PR to target the protected base, and
   require its merge commit to remain an ancestor of both the resolved base and
   current HEAD. This is deliberately stronger than a same-issue prose
   dependency, but does not claim to make a GitHub comment cryptographic
   evidence against a hostile repository owner.

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
- **Review churn can consume the run** → each chunk stops at five rounds and
  is recorded as blocked for later human triage.
- **A user enables too many mutations** → each action remains named, logged by
  the command output, and merge defaults to false.
- **A progress PR falsely unlocks a new same-issue budget** → a successor pins
  the controller-generated predecessor attestation and both Git revisions;
  missing, stale, retargeted, or non-ancestor evidence fails closed at every
  later action.

## Migration Plan

1. Install OpenSpec locally and initialize only its repository structure.
2. Commit the controller change and the disabled pilot manifest.
3. Run the local validation/tests and inspect the first preflight failures.
4. Enable a pilot only after the issue set, dependencies, branch protection,
   and the action policy have been reviewed.

## Open Questions

- Whether the final pilot should use stack mode with explicit merge authority or
  be split into independent issue batches remains a repository-owner decision.
