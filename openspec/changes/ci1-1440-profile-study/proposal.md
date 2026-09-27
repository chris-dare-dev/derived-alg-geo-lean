# Proposal

## Why

CI1.11 (#1440) has an offline Actions profiler and a conservative replay harness, but no reproducible live-run collector, current ranked bottleneck report, or bounded experiment against an independent cold reference. Existing Ubuntu timing notes are useful leads, not a matched study, and the runner resource limits are not measurements.

## What Changes

- Add a read-only GitHub Actions collector that records exact run and attempt identity, events, runners, jobs, steps, queue and phase timings, cache restore evidence, failure classes, and explicit unknowns.
- Add a read-only host sampler for one named self-hosted runner service and run identity; do not alter the service, workflow, cache, or runner configuration.
- Publish a reproducible, bounded warm-cache versus cold-target-build experiment on one exact commit and compare the target artifact hashes.
- Extend the offline replay matrix for direct/transitive dependencies and trust-boundary changes; keep replay opt-in and outside required CI.
- Publish ranked current bottlenecks and evidence-bounded concurrency/service-rate implications for four-to-six producers, with sample size, platform, cache, and measurement limits; if observations do not cover that load, record the gap and make no capacity claim. Leave rollout claims pending until #1436/#1438 are available.
- Add this manifest's exact digest to the owner-reviewed manifest list in a protected-path planning PR; run preflight only after that PR merges.

## Capabilities

### New Capabilities

- `ci1-live-profile`: Collect and report revision-bound CI performance evidence and a bounded cache experiment without activating an optimization.

### Modified Capabilities

None.

## Impact

The implementation change is limited to `scripts/ci_performance/`, its focused tests, `scripts/ci_performance/README.md`, and a report under `docs/ci/`. A preceding planning PR adds the manifest's exact digest to `LEGACY_REVIEWED_MANIFESTS` so the controller can authorize only the frozen paths in the manifest after owner review. It does not edit controller logic or standing authority. No change edits `.github/workflows/ci.yml`, `.github/workflows/cache-warm.yml`, `scripts/runner_state.py`, production audit entrypoints, Lean source, or cache policy. The implementation PR is progress toward #1440; the post-#1436/#1438 rerun remains open.
