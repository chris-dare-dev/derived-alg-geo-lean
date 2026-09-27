# Design

## Context

Issue #1440 is partially implemented by PR #1442: `scripts/ci_performance/profile_actions.py` profiles supplied job/step data and rejects unsafe replay identities. The live GitHub source collector, host-pressure time series, matched current phase study, and cold-reference experiment are still absent. The current checkout starts at `e83b614078d491b7f1d8dab085bf494fddb32ebc`; its successful main CI run is `36279634782`.

## Goals / Non-Goals

**Goals:**

- Preserve run ID, attempt, full commit, event, runner identity, platform, queue delay, per-phase duration, cache restore evidence, and job failure classification.
- Keep observations traceable to source run URLs and preserve missing telemetry as `unknown` with a reason.
- Compare one same-commit, same-target cold build with a cache-seeded build in separate worktrees; compare the target `.olean` hashes.
- Keep all profiling and replay work opt-in and read-only with respect to GitHub and runner services.
- Activate the scripts-touching manifest only after its exact digest is merged into the owner-reviewed list on `main`.

**Non-Goals:**

- Changing workflow routing, cache keys, production cache policy, audit commands, runner services, branch protection, or Lean source.
- Claiming that an Actions job API contains historical host utilization when no host sample was collected.
- Turning replay output into a CI gate or allowing it to skip required verification.
- Closing #1440 before the post-#1436/#1438 measurement refresh.

## Decisions

- The collector uses the authenticated `gh` CLI for Actions run, attempt/job, and selected build-job log reads. It stores normalized evidence and source URLs; it never writes provider state. Fetching logs is opt-in and limited to selected runs because logs can be large.
- The manifest's code chunk includes paths below `scripts/`, so a branch-authored manifest cannot preflight that work. A separate protected-path planning PR will add its exact digest to `LEGACY_REVIEWED_MANIFESTS`; the manifest stays `enabled`, but no run is started until the planning PR merges and the live preflight succeeds. The allowlist entry grants no controller logic or standing-authority change.
- The collector classifies cache state only from explicit cache log markers. Missing or ambiguous markers remain `unknown`; step success alone does not prove a cache hit. Restore cost uses the exact `Restore build output` step interval and available cache-size log value.
- The host sampler reads `/proc` pressure/load/memory and the named systemd user service's cgroup CPU and memory counters. It accepts a caller-supplied run/attempt and service name, records timestamps, and does not stop or restart the service. Samples from another service or outside the run interval are not attributed to that run.
- Step durations are aggregated as interval unions so parallel jobs do not double-count wall time. Reset, cache restore, Lake build, audit, emitter, contract, upload, and other steps remain separate. Comparisons state event, runner, cache state, and sample size; unmatched runs are descriptive only.
- Producer-capacity and service-rate implications use observed overlapping run intervals, queue delays, throughput, service intervals, and host-pressure samples, with the represented physical host and runner services named. No extra load is generated. If the current sample does not cover four-to-six concurrent producers, the report records the highest observed concurrency, identifies the missing evidence, makes no four-to-six capacity claim, and keeps #1440 open; service counts are not treated as capacity.
- The bounded experiment uses one named Lean target, one source commit, one toolchain/manifest/pin set, and separate cold and warm worktrees. Both execute `lake build <Target>` with a fixed thread cap; the warm worktree receives the existing no-hardlink cache seed, and the cold worktree has no `.lake/build`. The experiment reports timings and target artifact hashes without changing cache behavior.
- The existing replay model is treated as a fail-closed decision aid, not proof of a dependency graph. Fixtures cover direct and transitive changes, instance and axiom changes, emitter identity, pins/options, rename/deletion, and unknown inputs. Only complete exact identity can reach targeted replay; uncertainty returns full rebuild.
- This PR records a current snapshot and the experiment. A later refresh after #1436/#1438 is required before #1440 can close; no one-week post-rollout percentile is claimed now.

## Publication

The planning PR is an ordinary owner-reviewed bootstrap because it touches `scripts/loop_engine.py` and the run's manifest is not yet on the default branch's allowlist. Its trust-review label is a human review gate; do not self-apply it. After merge, resolve the exact current main SHA and successful CI run, rerun manifest validation and preflight, then work the implementation chunk on its configured `agent/ci1-1440-profile-implementation` branch.

## Risks / Trade-offs

- GitHub run/job data does not include host pressure or reliable cache-hit status. The report keeps those fields explicit and supplements only a live, correctly identified self-hosted sample.
- The first study spans a short window compared with a one-week rollout target. Current p50/p95 values are descriptive and do not certify service rate or reliability. If the sample lacks four-to-six concurrent producer windows with host telemetry, #1440 remains open for that measurement.
- A target `.olean` hash comparison is a bounded cache parity check, not proof that general dependency-based skipping is sound. Replay remains offline and full CI continues to verify every PR.
