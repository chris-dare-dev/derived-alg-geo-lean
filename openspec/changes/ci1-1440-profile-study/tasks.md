# Tasks

## 1. Capture reproducible live evidence

- [ ] 1.0 Add the exact execution manifest digest to the owner-reviewed manifest list in a protected-path planning PR; wait for merge and current-main CI, then rerun validation/preflight.
- [ ] 1.1 Add a read-only `gh` Actions collector and tests for pagination, run-attempt identity, job/step timing, cache log classification, and failure classes.
- [ ] 1.2 Add a self-hosted host-pressure sampler that binds samples to one run/attempt and runner service without changing service state.
- [ ] 1.3 Collect a stratified current run sample and preserve sanitized raw metadata plus source run links.

## 2. Run the bounded experiment and report

- [ ] 2.1 Extend replay fixtures for direct/transitive, instance, axiom, emitter, pins/options, rename/deletion, and unknown-input cases.
- [ ] 2.2 Run same-target cold and seeded-cache builds on one exact commit and compare elapsed time and the target `.olean` digest.
- [ ] 2.3 Publish ranked bottlenecks, sample/hardware/cache limits, missing host telemetry, and a go/no-go; keep production verification unchanged.
- [ ] 2.4 Review the exact progress commit with four independent roles, pass hosted CI, and publish `Progress toward #1440` without closing the issue.
- [ ] 2.5 Re-run measurements after #1436/#1438 before final issue closure.
