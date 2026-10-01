# CI performance observations and replay harness

`collect_actions.py` makes a read-only snapshot of one GitHub Actions run
attempt. It requires a completed run and attempt, fetches every page of attempt
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
For both entry points, phase times are unions of intervals: concurrent phases
can overlap, and they must not be summed as a partition of wall time. Workflow
start delay, prerequisite wait, scheduler gap after a job is eligible, and
runner queue are distinct. A negative timestamp interval is retained as an
anomaly with unknown duration for its phase. Jobs carried forward from a prior
run attempt remain in the raw capture and profile inventory, but contribute no
time or failure outcome to the selected attempt. A cancelled or timed-out run
is not counted as a successful build. An executed terminal job with no steps
has unknown work phase durations. A prior-attempt job must finish before the
selected attempt was created; an overlapping job whose attribution is unclear
makes attempt wall and phase durations unknown. The selected attempt's platform
uses only attributed current jobs. A run with no terminal job cannot form a
completed profile.

`profile_actions.py replay <case.json>` is a conservative, offline decision
harness. It compares explicit base and candidate toolchain, manifest, target,
options, pins, emitter, instance and exported-axiom identities, and requires
full revision SHAs, a complete change inventory and dependency graph, and
explicit changed-file classification. Changed or absent identity, renames,
deletions, unknown inputs,
noncanonical or out-of-repository paths, or incomplete classification force
`full_rebuild`. `targeted_replay` is only an
experiment candidate; it does not authorize skipping a required gate. A
matched independent cold/full reference remains necessary before proposing
production reuse. The complete-graph and complete-change flags are caller
assertions, not validated graph or diff provenance. This tooling does not edit
workflows, caches or checks.
