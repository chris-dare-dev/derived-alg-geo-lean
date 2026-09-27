# CI1.07 exact-tree Ubuntu routing sample, 2026-09-27

This is a read-only progress measurement for #1436. It changes no workflow,
runner service, admission limit, branch protection or cache policy. Windows
retirement and the hosted-PR/self-hosted-main routing were already applied in
[#1443](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1443).
The three pairs below test gate outcomes on equal Git trees; they do not
establish cold-build parity, shared-host capacity or a rollout decision.

## Identity and collection

For each merged PR, the first-attempt hosted `pull_request` run and the
first-attempt self-hosted `push` run completed successfully. GitHub's run
`head_sha` identifies the PR source head, while the PR's trust-artifact name
identifies the synthetic merge commit actually tested. I fetched that commit
through the Git API, checked its second parent against the PR head, and
compared its Git tree with the published main commit's tree. The workflow blob
and gate-inventory blob also agree *within* each pair. The three workflow
blobs are all `cd8c6a4946bcb0e2c2167629ae9c8b232794ef80`; the inventory
was schema 5 for the first two pairs and schema 6 for the third. The required
`build`, `roadmap` and `ci` jobs are present in both versions.

The owner-local archive at
`~/.loop-runs/transcripts/analysis/2026-09-27-m54-recovery/probes/1436-routing-parity/`
contains the raw run and [attempt](https://docs.github.com/en/rest/actions/workflow-runs#get-a-workflow-run-attempt)
responses, complete [attempt-job pages](https://docs.github.com/en/rest/actions/workflow-jobs#list-jobs-for-a-workflow-run-attempt),
artifact listings and subject commits, six build logs, a semantic comparison
of one artifact pair, analysis scripts and `SHA256SUMS`. All 63 archived files
verify with `sha256sum -c SHA256SUMS`. `summary.json` has SHA-256
`8fda0ac2ce700b9ff077ff0cb8db6de1faf1db2d18b1115db0273258bad73c1c`.

| PR and change | Hosted PR run | Main push run | Tested tree | Main build queue, hosted / self-hosted | Build execution, hosted / self-hosted |
| --- | --- | --- | --- | ---: | ---: |
| [#1606](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1606), cross-module Lean and audit | [36337863251](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36337863251) | [36339314603](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36339314603) | `f8e982e140c4715f4623d805acf04e57946aab65` | 3 / 1343 s | 1393 / 887 s |
| [#1609](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1609), runner admission paths | [36339562967](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36339562967) | [36341221828](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36341221828) | `96ebc376d36d1444935ab511e6e7c5da5cde67b5` | 3 / 393 s | 1579 / 888 s |
| [#1615](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1615), security contract and evidence | [36343539052](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36343539052) | [36345139654](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36345139654) | `8777d3edc3eb2e68a700c489a43a23286339350b` | 3 / 1 s | 1541 / 917 s |

Queue is the job's `created_at` to `started_at`; execution is `started_at` to
`completed_at`. It is not a run-created-to-run-started proxy. The self-hosted
queue ranges from one second to 22 minutes 23 seconds in these three samples;
the hosted queue is three seconds each. The small sample cannot estimate a
service-rate distribution, and a run's delayed job cannot by itself identify
CPU, memory, disk or runner-availability causation.

## Gate and artifact observations

For every pair, `build`, `roadmap` and aggregate `ci` succeeded on both lanes.
Each job had the same ordered step names and conclusions across its two runs:
36/36 build steps, 6/6 roadmap steps and 3/3 aggregate steps, all `success`.
That includes the algebraic-geometry, stability-condition and DG axiom audits,
audit completeness, single instantiation, linters, warning and style ratchets,
source/ownership/umbrella checks, the no-`sorry` gate, the emitter, contract
gates, emitter reproducibility and artifact upload. The PR `build` jobs ran on
GitHub Actions hosted runners; the main `build` jobs ran on
`chris-ubuntu-main-runner`. The roadmap and aggregate jobs ran on hosted
runners in both lanes. This is observed outcome parity, not proof that all
internal artifacts have identical raw bytes.

I downloaded the trust artifacts for the #1606 pair for a closer comparison.
The algebraic-geometry, stability-condition and DG audit records have equal
name-and-axiom multisets (5578, 7287 and 1373 records respectively). The
first two raw audit files differ in record order; the DG file is byte-equal.
The two emission files have the same ordered 31,904 constants, modules and
counts. The declaration files have the same ordered 31,904 declarations and
counts. Their source-commit and emission-time fields differ as expected
between a synthetic PR merge and a main squash commit, and dependent hashes
therefore differ. The environment digests are equal; `attest/build.json` is
byte-equal. The raw comparison is `pr-1606/artifact-parity.json` in the archive
(SHA-256 `93e797c8165295300f6bc69863753c716f4ca649cdffc465e39a1d5570862d94`).
The other two pairs have gate-outcome parity but no cross-run artifact-content
comparison in this slice.

All six archived build logs say `Cache restored from key`, so this is a
**warm-cache sample**. The keys and logs are retained; a successful restore
does not prove that every source artifact was reused. Hosted and self-hosted
machines differ, and no per-job PSI, cgroup CPU/memory trace or disk-pressure
series was available for these completed runs. `host-snapshot.json` records
only a later point-in-time host configuration and pressure sample, not the
conditions of the six jobs. The four Ubuntu runner services share one physical
host, as the [runner runbook](ubuntu-runners.md) states; four labels are not
four independent capacity pools.

## Boundary and next measurement

At collection time, branch protection required only `ci`, with strict
up-to-date checking. The sampled PR build runners were hosted and the sampled
main build runners were self-hosted. The workflow has no
`pull_request_target` trigger. This read-only observation does not change
protection or prove a rollback. The auxiliary cache-warm workflow and dynamic
security check are separate from these three required CI jobs; their status
must not be inferred from a successful `ci` aggregate.

The next #1436 slice needs #1435's isolated job pickup and #1434's admission
contract before a routing cutover. Capture per-physical-host queue, cgroup
CPU/RAM and disk/PSI during named concurrent jobs; run a controlled
cancellation/restart and a cold/warm matched revision; then rehearse the
reviewed hosted-routing rollback and attach exact PR and main run identities.
Until those results exist, keep the current routing and capacity limits and
leave #1436 open.
