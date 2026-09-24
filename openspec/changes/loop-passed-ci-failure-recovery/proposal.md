# Proposal

## Why

The loop controller currently offers up to two post-pass revalidation panels for changed commits, but they are separate from `max_review_rounds_per_chunk` and do not require evidence of a failed required check on the exact live pull-request head. This leaves CI-driven code repair insufficiently tied to its cause and can let critique/revise panels exceed the frozen chunk cap; PR #1471 exposed the gap after its first panel passed and hosted CI failed.

## What Changes

- Add a fail-closed, append-only transition in the existing ordinary ledger that records a completed failure of a check required by both the frozen manifest and live branch protection on the exact head of the matching open pull request.
- Permit a repair panel only if an original review slot remains; charge the complete four-role panel to the frozen cap and preserve all earlier review evidence.
- Record cap exhaustion in that same ledger as terminal and non-publishable without rewriting its prior pass. Resolve the same ledger explicitly for push and issue closure, and deny every publish/close action while repair review is pending.
- Require a passing exact-head panel and green required checks on the current pull-request head before merge eligibility.
- Document the distinction between CI-failure repair and existing protected-base revalidation, and log the observed workflow gap.
- Keep historical manifests and ledgers unchanged; the separately scoped issue #1483 bootstrap manifest keeps all provider mutation flags disabled.

## Capabilities

### New Capabilities

- `loop-engineering`: Evidence-bound, cap-charged review continuation after a required CI failure for a passed loop chunk. This creates a new in-flight capability slice at the established path; `openspec list --specs` reports no archived canonical capability spec.

### Modified Capabilities

- None.

## Impact

The change affects `scripts/loop_engine.py` and its CLI, its focused Python tests, the loop recovery and manifest workflow documentation, and the frozen issue #1483 manifest. The existing ordinary ledger is the sole state authority; no parallel registry is added. It adds no Lean declarations, imports, public API, or mathematical claims. PR #1471 and issue #554 are motivating evidence only and remain outside this change's implementation scope.
