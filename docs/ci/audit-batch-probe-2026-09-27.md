# Bounded audit batching probe, 2026-09-27

This is a read-only experiment toward #1440, not a replacement for any CI
gate. It ran at `0510801da3e578b3cfa0ea90628b8265ae7c8cd3` on
`chris-dare-ubuntu` (16 logical CPUs, 65.37 GB physical memory). Every direct
import's `.olean` existed before the probe. The OS page-cache state and other
host activity were not controlled, so these are prebuilt-cache observations,
not a cold/full reference or a CI speed claim. No audit source or production
entrypoint was changed.

Raw commands, generated Lean sources, stdout/stderr, timestamped pressure
samples, and SHA-256 checksums are in the owner-local archive
`~/.loop-runs/transcripts/analysis/2026-09-27-m54-recovery/probes/1440-final-audit/`.
Its `summary.json` has SHA-256
`f1d9b919b08cff76f81623c5052a43d73b0d7a34521df801d0b0980f3884a06e`.
Run
`sha256sum -c SHA256SUMS` there to verify the archive. The archive's
`generate_batch.py --repo-root <checkout-at-the-recorded-revision>` recreates
the exact aggregate sources from `metadata.json` and the repository files.
The separate-file commands use
`LEAN_NUM_THREADS=2 ~/.elan/bin/lake env lean <audit slice>`, and the batch
commands use the generated files at the same revision.

## Selection and timing

For each of the AlgebraicGeometry and StabilityCondition area audits, the probe
chose the files nearest the 10th, 30th, 50th, 70th and 90th percentile by
number of `#print axioms` commands among files whose direct imports had
prebuilt `.olean`s (100 and 74 eligible files). The selected counts were
`1, 4, 9, 18, 67` and `1, 6, 18, 74, 272`. The exact paths and imports are in
`metadata.json`. An import-only file contained just that slice's import lines;
the full run used the unmodified area audit. Two passes reversed full/import
order. The timing loop polled at 250 ms, so these ten-file totals are
approximate.

| Ten separate files | Pass 1 | Pass 2 |
| --- | ---: | ---: |
| Full audit sources | 17.275 s | 17.025 s |
| Import-only sources | 17.274 s | 15.772 s |

Across both passes, import-only time was 96.3% of full-file time. That makes
shared import loading worth a bounded trial; it does **not** show that simply
importing the audit files would replay their output. `#print axioms` emits
records only when elaborated in the current file.

The prototype therefore put each file's full body in its own `section` after
one deduplicated import list, preserving the `#print axioms` commands. The
first ten-file run hit its 40-second cap because the probe captured stdout in
a 65,536-byte pipe and drained it only after the child exited. Its output
stopped at exactly that capacity, midway through the 70,166 expected bytes;
its flat RSS samples are consistent with the child blocked on output. **That
run measures a probe defect, not Lean execution time.** It remains in the raw
archive with its diagnosis.

The corrected probe redirected stdout and stderr to files while Lean ran. It
completed twice, in 2.957 and 2.689 seconds, against 17.275 and 17.025
seconds for the separate-file passes. Its output was byte-identical to the
concatenated independent output on both passes. `scripts/check_audit.py`
accepted all 470 records against 470 `#print axioms` commands. Peak sampled
process-tree RSS was 5.63 and 5.60 GB. The warm descriptive time saving was
82.9–84.2%; this is an experiment result, not a production CI speed claim.
The rerun used a later commit with no changes in `DerivedAlgGeo/`, the selected
audit sources, Lean/Lake pins or the audit parser; the archive records the
exact revisions and checked path set.

Two smaller groups completed twice. The independent reference in each row is
the sum of separate, fresh Lean processes on the same sources and revision.
The batched stdout was byte-identical to their concatenated output on both
passes, with order and record count preserved.

| Group | Separate, passes 1 / 2 | Batch, passes 1 / 2 | Descriptive saving | Audit parser |
| --- | ---: | ---: | ---: | --- |
| Two AG files, 5 records | 3.097 / 3.171 s | 1.791 / 1.769 s | 42–44% | 5/5, pass |
| Two stability files, 346 records | 4.331 / 5.086 s | 2.384 / 2.505 s | 45–51% | 346/346, pass |

The two output SHA-256 values were stable across passes:
`a0629e201cbf79339f10db78a987c640711fd8c0bfc717d6c11c2aa78cae085f`
for AG and
`14e284da7d9a94a690951a9f5c83e8264ab53d15942757bf4fa538f6e6b3a1a3`
for stability. `scripts/check_audit.py <batch-output> <batch-source>` passed
both groups, including its command-count and allowed-axiom checks. The
observed savings are **1.3–2.6 seconds per pair** in these warm samples; they
cannot be multiplied over the full audit without a representative grouping,
memory budget, and independent cold/full parity result.

During the separate-file runs, host-wide PSI `some avg10` ranged from
0–0.18% CPU, 0–0.38% memory and 0% IO. Those timestamped values are tied to
the named host and probe commands, but reflect all host processes and cannot
be assigned to this experiment alone. This environment exposed no
`/sys/fs/cgroup/memory.current`; process-tree RSS is the specific memory
observation for both the invalid capped run and the corrected runs. Hosted
PR runner pressure remains unknown.

## Decision and remaining evidence

Do not activate batching in required CI yet. Ten-file and two-file groups both
merit a separately scoped, cold/full parity study. The ten-file grouping has
the larger warm saving but uses about 5.6 GB RSS in one process, so its
concurrent host budget must be measured. The study must compare normalized
records, order, count, parser verdict, exit status and elapsed time across the
complete affected audit, including a cold build and warm rerun on a matched
revision, with concurrent host work and memory use recorded. A mismatch or a
memory/time regression is a no-go. These bounded warm results support further
measurement, not production activation.

The earlier [CI baseline](performance-baseline-2026-09-27.md) ranks audits and
emitter work, but does not isolate reset subcommands or emitter costs on
matched cold/warm revisions. Its cache state and hosted pressure are unknown.
#1436 and #1438 remain open, so their post-rollout measurement and #1440's
closure report remain to do. The offline replay harness is not used by any
required gate; its cross-revision dependency and change-inventory claims are
still caller assertions, and no reuse optimization was selected here.
