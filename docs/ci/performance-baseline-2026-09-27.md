# CI performance baseline, 2026-09-27

This is a measured baseline toward #1440, not a controlled benchmark or a
production optimization. The sample was captured from the `CI` workflow
between 07:05 and 14:34 UTC on 2026-09-27. It has 12 successful `push` runs on
the owner's self-hosted Ubuntu runner and the 12 most recent `pull_request`
runs on GitHub-hosted Ubuntu (8 successful, 4 cancelled). Every run is attempt
1. The archived raw run, job and step responses, analysis code and logs are in
`~/.loop-runs/transcripts/analysis/2026-09-27-m54-recovery/probes/1440-performance/`
on the owner's machine. The read-only collector in
`scripts/ci_performance/collect_actions.py` can recapture each run ID, and
`profile_actions.py profile-bundle` normalizes its attempt. The archive is
local evidence, while the run links below are provider evidence.

| Lane | Successful build jobs | Median build wall | Range | Median full run |
| --- | ---: | ---: | ---: | ---: |
| `push` | 12 | 14m12s | 14m03s–14m39s | 14m20s |
| `pull_request` | 8 of 12 | 26m16s | 20m58s–27m23s | 26m25s |

Sample run IDs (each resolves at
`https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/<id>`):

- `push`: 36302035784, 36303477905, 36304907474, 36306357256,
  36308816190, 36310600345, 36313240482, 36315269553,
  36316979344, 36319040483, 36320975197, 36322935398.
- `pull_request` successful: 36313857075, 36315438735, 36315637318,
  36317471576, 36319461934, 36321356380, 36324696907, 36325066707.
  Cancelled: 36314870334, 36325549451, 36326273568, 36326329164.

For a reproduction, capture a run with `collect_actions.py --repository
chris-dare-dev/derived-alg-geo-lean --run-id <id> --output <new-file>` and
profile it with the `ci-job-needs.json` map after checking the workflow at
that run's SHA. The captured JSON and sidecar retain run, attempt, SHA, event,
job labels, timestamps, steps and conclusions. GitHub's Actions API has no
per-run memory, CPU, cache-hit, or cold/warm field. This sample's cache state
and host pressure are therefore **unknown**; the runner's documented 3 CPU
thread cap and 12 GiB memory reservation are configuration, not utilization
measurements. A slow `lean-action` step does not establish a cold build.

## Ranked work in the build job

The categories below are shares of the *sum of successful build-job wall
times* in each lane. They are descriptive, not savings promises. Concurrent
jobs are not added to one another when calculating a run's phase wall time.

| Rank | Category | `push` share | `pull_request` share | Representative step medians |
| --- | --- | ---: | ---: | --- |
| 1 | Audits, including completeness and single-instantiation | 49.3% | 42.1% | AG axiom 3m22s / 4m58s; stability axiom 2m16s / 3m18s |
| 2 | Emitter and reproducibility | 36.0% | 35.2% | emit environment 2m35s / 4m44s; reproducibility 2m33s / 4m36s |
| 3 | `leanprover/lean-action` | 2.5% | 9.6% | 21s / 2m07s |
| 4 | Contract gates | 5.8% | 5.2% | 49s / 1m24s |
| 5 | Environment linters | 2.2% | 4.7% | 19s / 1m16s |

The order in the table follows the hosted PR lane, the required premerge
path; the main-only order puts contract gates ahead of `lean-action`.
`Reset the tree, keeping .lake` was 0–1s in these jobs. One logged `du`
traversal over an 11 GiB tree took about 0.7s. The old Windows estimate that
reset plus AG/stability audits took about 61% came from a different runner and
workflow, so it does not describe the current reset cost. Audit loops over
103 AG and 76 stability files took 5.6min (`push`) and 8.6min (PR) in one
logged pair. Those are whole-loop time **ceilings** on possible batching
savings; `#print axioms` output does not replay across imports, so merely
importing the audit files is not a valid batching experiment.

The `ci` aggregation job depends on `build` and `roadmap`. Its creation occurs
after those prerequisites on current GitHub responses. The 14–26 minute span
from workflow creation to its start is mainly **dependency wait**, not runner
queue. In this sample the build job's creation-to-start wait was 2–3s on main
and 3–44s on PRs. Historical main bursts exceeded 43 and 57 minutes of
runner wait, so this short sample is not a capacity guarantee. One cancelled
run, [36326329164](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36326329164),
has a `ci` job completion timestamp one second before its start. The profiler
retains that anomaly and leaves the duration unknown.

## Four to six producers

The current branch protection requires `ci` on an up-to-date PR head. As an
optimistic serial merge model, one hosted premerge cycle of 26m16s gives at
most about **2.3 merges per hour** if each merge invalidates the next PR's
base. The single main runner's 14m12s build gives about **4.2 pushes per
hour** when continuously occupied. Neither number is observed merge
throughput; reruns, conflicts, queue bursts and cache misses lower it.

If four producers each propose one merge candidate every two hours, the
arrival rate is 2/h and sits just below the optimistic premerge rate. Six at
the same pace produce 3/h, exceeding it by about 0.7/h. At one candidate per
producer per hour, 4–6/h also approaches or exceeds the main runner's 4.2/h
service rate. Adding runner processes alone cannot remove strict-base
premerge reruns or make audit/emitter work disappear. The sampled maximum was
three simultaneous build jobs (one push, two PR); the 4–6-producer cases are
explicit scenarios, not measured arrivals.

## Next experiment and limits

Choose one bounded, offline audit-traversal prototype only after profiling
the per-file loop on matched revisions and confirming whether the repeated
elaboration can be shared without losing any `#print axioms` output. Compare
its results with independent cold/full verification, including direct and
transitive imports, instances and exported axioms. The replay harness fails
closed on changed or missing identity, renames, deletions and unknown inputs;
it is not a replacement for that parity test. Record a go/no-go decision and
exact cost/benefit before any production workflow change. Rerun this baseline
after #1436 and #1438, which are still open. This progress slice does not
close #1440.
