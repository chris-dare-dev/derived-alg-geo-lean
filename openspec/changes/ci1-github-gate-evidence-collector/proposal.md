# Proposal

## Why

CI1.01 (#1430) has a schema v4 inventory and validator, but no code collects the GitHub evidence that the validator consumes. A hand-authored record can pass its consistency checks without proving that the current PR candidate actually received the required CI results. This gap blocks safe adoption by the integration controller.

## What Changes

- Add a read-only GitHub collector that obtains the current protected base, PR head, tested candidate, workflow run, check runs, and commit statuses from provider responses, then produces schema v4 evidence for the existing validator.
- Fetch complete paginated observations, preserve producer and run-attempt identities, and deny an admission claim when provider metadata is missing, ambiguous, stale, or truncated.
- Add focused provider-response fixtures and a read-only current-PR exercise. Document the source of each trusted field and the limits of the evidence claim.

This is a progress change for #1430. It does not edit CI workflow routing, `scripts/loop_engine.py`, branch protection, reviewer policy, or Lean source. The controller consumer belongs to #1434, and workflow adoption requires its own scoped change. A collected record alone does not authorize a merge or close #1430.

## Capabilities

### New Capabilities

- `ci-gate-evidence-collection`: Produce candidate-bound, provider-sourced CI evidence with complete observations and fail-closed behavior for the existing gate contract.

### Modified Capabilities

None.

## Impact

The proposed implementation adds a GitHub adapter under `scripts/`, focused tests under `scripts/tests/`, and updates `docs/ci/gate-evidence-contract.md`. It reads GitHub API responses and immutable Git objects without changing repository settings or mathematical code. Because `scripts/` is protected from branch-authored unattended loop manifests, this change follows the same bounded plan and exact-revision review discipline through an ordinary owner-reviewed PR; it does not relax the loop controller's path policy.
