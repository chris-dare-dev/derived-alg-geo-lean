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
`0a7ec6b5b92947bab4d8e2753989f594dcb679ad048a363aaa5ffc6e97ba4e93`.
Run `sha256sum -c SHA256SUMS` there to verify all 123 files. The archive's
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
one deduplicated import list, preserving the `#print axioms` commands. A
ten-file aggregate exceeded a **40-second cap** after outputting 65,536 of
70,166 expected bytes; its process tree reached 5.69 GB RSS. One separate-file
pass took 17.0–17.3 seconds. The ten-file grouping is a **no-go** on this
measurement: it was slower even at the cap and did not complete. The archived
run has the termination reason and samples; it was not counted as a parser
pass.

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
`/sys/fs/cgroup/memory.current`; the capped batch's process-tree RSS is the
specific memory observation. Hosted PR runner pressure remains unknown.

## Decision and remaining evidence

Do not batch ten area files or activate any batching in required CI. Two-file
grouping is a candidate for a separately scoped, cold/full parity study. That
study must compare normalised records, order, count, parser verdict, exit
status and elapsed time across the complete affected audit, including a cold
build and warm rerun on a matched revision, with concurrent host work and
memory use recorded. A mismatch or a memory/time regression is a no-go. The
current pairwise result is a reason to study that scope, not a production go.

The earlier [CI baseline](performance-baseline-2026-09-27.md) ranks audits and
emitter work, but does not isolate reset subcommands or emitter costs on
matched cold/warm revisions. Its cache state and hosted pressure are unknown.
#1436 and #1438 remain open, so their post-rollout measurement and #1440's
closure report remain to do. The offline replay harness is not used by any
required gate; its cross-revision dependency and change-inventory claims are
still caller assertions, and no reuse optimization was selected here.
