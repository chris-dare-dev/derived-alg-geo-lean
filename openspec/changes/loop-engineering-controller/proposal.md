# Proposal

## Why

The repository's Lean builders and GitHub runners are the slowest part of a
multi-issue formalization loop. We need a durable plan and review ledger that
lets an already-authorized session make progress across a small batch without
turning unattended execution into an unbounded or mathematically unsafe agent.

## What Changes

- Add OpenSpec as the repository-owned home for proposals, requirements,
  designs, and task checklists.
- Add a bounded loop controller that validates a run manifest, performs a
  read-only preflight, records independent reviews, and guards remote actions.
- Require mathematical, repository-boundary, abstraction, and style review for
  each frozen implementation chunk, with no more than five review/improve
  rounds per chunk.
- Keep GitHub comments, issue closure, pushes, pull-request creation, approval,
  and merging as separately named manifest capabilities.

## Capabilities

### New Capabilities

- `loop-engineering`: bounded, spec-driven execution and review control for
  Lean formalization batches.

### Modified Capabilities

- None.

## Impact

The change adds Python control-plane code, OpenSpec planning artifacts, three
adversarial reviewer roles, repository documentation, and cheap local gates.
It does not perform any GitHub mutation until the enabled pilot passes its
clean-checkout, dependency, branch-protection, and roadmap preflight.
