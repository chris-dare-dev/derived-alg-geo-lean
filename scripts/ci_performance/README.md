# CI performance observations and replay harness

`collect_actions.py` makes a read-only snapshot of one GitHub Actions run
attempt using GitHub's [run-attempt](https://docs.github.com/en/rest/actions/workflow-runs#get-a-workflow-run-attempt)
and [attempt-jobs](https://docs.github.com/en/rest/actions/workflow-jobs#list-jobs-for-a-workflow-run-attempt)
endpoints. It requires a completed run and attempt, fetches every page of attempt
jobs, then re-reads the run to reject a changing identity or status. Schema 2
retains each response envelope with its request URL, headers, Link relations,
advertised count, and job objects alongside the flattened inventory. It stores
the provider JSON and a SHA-256 sidecar. The digest detects accidental edits;
it is not a signature or a CI verdict. Choose a new output path for every
capture. A GitHub token with Actions read permission is required.

```bash
python3 scripts/ci_performance/collect_actions.py \
  --repository chris-dare-dev/derived-alg-geo-lean --run-id 36336924056 \
  --output scratch/run-36336924056.json
python3 scripts/ci_performance/profile_actions.py profile-bundle \
  scratch/run-36336924056.json \
  --job-needs scripts/ci_performance/fixtures/ci-job-needs.json \
  --output scratch/profile-36336924056.json
```

For this revision of `ci.yml`, the separate `ci-job-needs.json` file contains
`{"build": [], "roadmap": [], "ci": ["build", "roadmap"]}`. Verify that map
against the exact workflow revision before using it; the Actions jobs API does
not include the `needs` graph. Without a graph, dependency wait and runner
queue are `null`, while the observed job creation-to-start wait remains. The
profile records run ID, attempt, SHA, event, runner labels/name, status and
conclusion. It labels cache state and host pressure unknown unless measured
separately. It never infers a cold build from a slow step or a runner failure
from a failed job conclusion.

`profile_actions.py profile <run.json>` accepts a normalized offline fixture.
The normalized profile is schema 3; the raw provider capture remains schema 2.
For both entry points, phase times are unions of intervals: concurrent phases
can overlap, and they must not be summed as a partition of wall time. Workflow
start delay, prerequisite wait, scheduler gap after a job is eligible, and
runner queue are distinct. A negative timestamp interval is retained as an
anomaly with unknown duration for its phase. Before aggregation, each job is
classified `selected`, `carried` or `uncertain` using its execution interval
and the selected attempt's creation and start timestamps. A valid job ending
before *both* attempt boundary timestamps is carried; one starting after
*both* is selected. Missing or inverted endpoints, a partial step timestamp
outside the job interval, or a job crossing the boundary is uncertain. The job
`run_attempt` and `created_at` fields are inventory, not execution proof:
GitHub can relabel carried jobs on a later attempt. A missing boundary makes
attribution uncertain instead of fabricating a number.

Carried jobs remain in the inventory but contribute no selected-attempt time,
failure or platform. Uncertain jobs retain raw conclusion and reason in a
separate inventory; their failures are reported separately, and potentially
affected wall and phase durations are `null`. A selected non-skipped terminal
job with no steps has unknown work phases, even if its rounded start and end
timestamps are equal. Incomplete or zero-length step timestamps likewise
leave their phase unknown. A cancelled or timed-out run is not counted as a
successful build. Platform uses only selected jobs and is unknown when any
attribution remains uncertain. A capture with no selected terminal job can
still yield an `attribution_uncertain` profile when a terminal job is present
but cannot be attributed; otherwise it is rejected as incomplete.

`profile_actions.py replay <case.json>` is a conservative, offline decision
harness. It compares explicit base and candidate toolchain, manifest, target,
options, pins, emitter, instance and exported-axiom identities, and requires
full revision SHAs, a complete change inventory and dependency graph, and
explicit changed-file classification. Changed or absent identity, renames,
deletions, unknown inputs,
noncanonical or out-of-repository paths, or incomplete classification force
`full_rebuild`. `targeted_replay` is only an offline hypothesis while its
complete-graph and complete-change flags are caller assertions; it does not
authorize skipping a required gate. A
matched independent cold/full reference remains necessary before proposing
production reuse. The complete-graph and complete-change flags are caller
assertions, not validated graph or diff provenance. This tooling does not edit
workflows, caches or checks.

The dated [CI baseline](../../docs/ci/performance-baseline-2026-09-27.md)
and [bounded audit batch probe](../../docs/ci/audit-batch-probe-2026-09-27.md)
give the measured context and remaining cold/full parity obligation for #1440.
