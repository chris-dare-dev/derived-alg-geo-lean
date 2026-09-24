# Proposal

## Why

Milestone 13 consists of the parent issue #137 and its two deliverables: the reusable topic template (#182) and the reduced second-topic gate (#183). The issue bodies define the scope. The user explicitly asked to complete all three and bootstrap an issue-first loop, so the `gate:owner` labels are not waiting for another authorization step.

## What Changes

- Finish the Copier template with an optional anchor, direct Mathlib pin fallback, complete saved answers, honest metadata, and zero Bridgeland-specific template bytes.
- Demonstrate the template in an anchor-free analytic-number-theory adopter.
- Pass the reduced gate with one fetched and ingested arXiv paper, five sourced registry entries including a digest-only Iwaniec–Kowalski contents locator, and an exact external binding to `Nat.infinite_setOf_prime` in the pinned Mathlib environment.
- Mark the reusable template's own trust record validated with dated gate evidence; keep each newly generated topic's trust record false by default.
- Record the issue-first loop procedure: issue acceptance drives the work; a second repository plan, contact email, generated manifest, or separate owner reauthorization is not a prerequisite.

## Capabilities

### New Capabilities

- `topic-template-gate`: reproducible generation and a falsifiable second-topic demonstration.
- `issue-first-loop`: a user-requested issue list is sufficient to begin scoped implementation and continue across participating repositories.

### Modified Capabilities

- None.

## Impact

Implementation spans MathFormalContract (template and tooling), arXMCP (source fetch and corpus), and a generated analytic-number-theory adopter. DerivedAlgGeo owns the milestone issues and this compact progress record. No public `DerivedAlgGeo` Lean API changes.

Use repository-native branches and pull requests where code belongs. One batch record is enough; do not create per-repository OpenSpec roots or manifests just to start. Keep normal correctness checks, hosted CI, branch protection, and the repository's trust review for protected paths. Those checks report actual code or platform constraints rather than planning prerequisites.
