# Spec Delta

## ADDED Requirements

### Requirement: Collection SHALL preserve exact run and attempt evidence

The read-only collector SHALL record the run ID, attempt, full head SHA, event, creation/start/completion times, runner labels/name, job and step identities, conclusions, source URLs, and available phase timings. It SHALL classify unavailable runner pressure, cache state, or restore size as unknown with a reason.

#### Scenario: Cache state is absent from the provider response
- **WHEN** a restore step succeeds but its log does not contain an unambiguous cache hit or miss marker
- **THEN** the report labels cache state `unknown` and does not infer warm state from step success

#### Scenario: A run has no terminal job
- **WHEN** a run is queued or in progress and has no completed job
- **THEN** the collector preserves it as pending and does not report a failed profile

### Requirement: Phase profiles SHALL separate work and disclose comparisons

The profiler SHALL report queue, checkout, reset, cache restore, Lake build, audit, emitter, contract, upload, and other intervals separately. It SHALL use interval unions for parallel jobs and identify comparison sample size, event, platform, runner, cache state, and missing fields.

#### Scenario: Two runs do not match on commit and runner
- **WHEN** a timing comparison uses runs with different commit, runner, platform, event, or cache state
- **THEN** it SHALL label them unmatched/descriptive and SHALL NOT describe the difference as a controlled optimization result

### Requirement: The bounded cache experiment SHALL use an independent cold reference

The experiment SHALL run one named target from the same commit, pins, toolchain, target, options, and thread cap in separate cold and warm worktrees, and SHALL compare target artifact hashes and elapsed time. It SHALL leave workflows and production cache policy unchanged.

#### Scenario: Cold and warm target artifacts differ
- **WHEN** the target `.olean` hash differs between cold and warm worktrees
- **THEN** the experiment reports no-go and does not propose production cache reuse

#### Scenario: Cold and warm target artifacts match
- **WHEN** target artifact hashes match and both builds succeed
- **THEN** the report records only this bounded exact-identity result and does not claim general dependency-based skipping is sound

### Requirement: Replay SHALL fail closed across dependency and trust boundaries

The offline replay harness SHALL force a full rebuild for unknown identity or dependency inputs, incomplete direct/transitive classifications, instance changes, exported axiom changes, emitter changes, pin/option changes, renames, and deletions. Replay SHALL remain outside required CI.

#### Scenario: A change has incomplete dependency information
- **WHEN** any changed file is absent from the exact direct/transitive partition or the graph is incomplete
- **THEN** replay returns `full_rebuild`

### Requirement: CI1.11 SHALL preserve rollout and sample limits

The report SHALL state raw run identities, sample size, platform, cache and host pressure evidence, confounders, and a go/no-go result. #1440 SHALL remain open until measurements are refreshed after #1436/#1438 when those lanes are available.

#### Scenario: Post-rollout dependencies are still open
- **WHEN** #1436 or #1438 has not completed
- **THEN** the report marks the rollout refresh pending and does not close #1440 or certify one-week targets

### Requirement: Producer-capacity implications SHALL be evidence-bounded

The report SHALL quantify observed producer concurrency, queue delay, service intervals, throughput, and service-rate implications relevant to four-to-six concurrent producers. It SHALL identify the physical host and runner services represented by the sample, SHALL NOT infer capacity from the number of configured services, and SHALL NOT extrapolate beyond observed load without labeling the result as an estimate. If the evidence does not cover four-to-six concurrent producers, the report SHALL say that capacity is not yet measured, identify the missing observation, record no-go for a capacity claim, and keep #1440 open.

#### Scenario: Current sample does not reach four producers
- **WHEN** collected runs do not provide a representative window with four-to-six concurrent producers and corresponding host-pressure samples
- **THEN** the report discloses the highest observed concurrency, leaves four-to-six producer capacity unmeasured, makes no service-rate claim, and keeps #1440 open
