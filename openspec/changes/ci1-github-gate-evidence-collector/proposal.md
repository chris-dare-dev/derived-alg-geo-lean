# Proposal

## Why

CI1.01 (#1430) has a schema v4 inventory and validator, but no code collects the GitHub evidence that the validator consumes. A hand-authored record can pass its consistency checks without proving that the current PR candidate actually received the required CI results. This gap blocks safe adoption by the integration controller.

## What Changes

- Add a read-only GitHub collector that obtains the current protected base, PR head, tested candidate, workflow run, check runs, and commit statuses from provider responses, then produces schema v4 evidence for the existing validator.
- Fetch complete paginated observations, preserve producer and run-attempt identities, and deny an admission claim when provider metadata is missing, ambiguous, stale, or truncated.
- Add focused provider-response fixtures and a read-only current-PR exercise through a narrow `loop_engine.py` evidence command. Document the source of each trusted field and the limits of the evidence claim.

This completes the read-only evidence and controller demonstration needed to close #1430 after review and merge. It does not edit CI workflow routing, controller queue admission or merge decisions, branch protection, reviewer policy, or Lean source. Durable controller adoption belongs to #1434. A collected record alone does not authorize a merge.

## Capabilities

### New Capabilities

- `ci-gate-evidence-collection`: Produce candidate-bound, provider-sourced CI evidence with complete observations and fail-closed behavior for the existing gate contract.

### Modified Capabilities

None.

## Impact

The implementation adds a GitHub adapter under `scripts/`, a read-only `loop_engine.py` command, a narrow schema/inventory correction for a runless auxiliary check app, focused tests under `scripts/tests/`, and updates `docs/ci/gate-evidence-contract.md`. It reads GitHub API responses and immutable Git objects without changing repository settings or mathematical code. Because `scripts/` is protected from branch-authored unattended loop manifests, this change follows the same bounded plan and exact-revision review discipline through an ordinary owner-reviewed PR; it does not relax the loop controller's path policy.
