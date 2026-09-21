# CI performance profiler and replay experiment

`profile_actions.py profile <run.json>` normalizes an Actions run and its job
steps into queue, checkout, reset, cache restore, Lake build, audit, emitter,
contract, upload, and other durations. Phase times are the union of intervals,
not a sum of overlapping jobs. It records complete run/head/event identity,
terminal and pending jobs, wall-clock time, and failure classes without turning
a cancelled, timed-out, runner, or provider failure into a test result. A run
with no terminal job is rejected rather than reported as a failure.

`profile_actions.py replay <case.json>` is a conservative decision harness for
the one bounded cache/reuse experiment. Exact toolchain, manifest, target,
options, pins, emitter, and complete dependency-graph identity are required.
Renames, deletions, unknown inputs, or missing identity force `full_rebuild`.
Only an explicit, complete direct/transitive dependency classification whose
disjoint union exactly equals `changed_files` permits `targeted_replay`; an
unchanged exact identity may use `cache_reuse`. Any missing, duplicated, or
overlapping classification forces `full_rebuild`.

The tool is offline and opt-in. It is not a required CI gate, does not edit
`.github/workflows/ci.yml` or `cache-warm.yml`, does not save a cache, and does
not claim that a profiler sample is a controlled benchmark. Record run ID,
attempt, commit, event, platform, host pressure, and sample count in the
findings report before proposing any production reuse optimization.
